#define WLR_USE_UNSTABLE

#include <algorithm>
#include <any>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <format>
#include <functional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define private public
#include <aquamarine/backend/DRM.hpp>
#undef private
#include <aquamarine/buffer/Buffer.hpp>
#include <hyprland/src/config/shared/monitor/MonitorRuleManager.hpp>
#include <hyprland/src/Compositor.hpp>
#include <hyprland/src/debug/log/Logger.hpp>
#include <hyprland/src/desktop/view/WLSurface.hpp>
#include <hyprland/src/output/Monitor.hpp>
#include <hyprland/src/plugins/PluginAPI.hpp>
#include <hyprland/src/render/Renderbuffer.hpp>
#include <hyprland/src/render/OpenGL.hpp>
#include <hyprland/src/render/Renderer.hpp>
#include <hyprland/src/state/MonitorState.hpp>

extern "C" {
#include <xf86drm.h>
#include <xf86drmMode.h>
}

static HANDLE         g_pluginHandle             = nullptr;
static CFunctionHook* g_needsUnmodifiedCopyHook  = nullptr;
static CFunctionHook* g_saveBufferForMirrorHook  = nullptr;
static CFunctionHook* g_getOrCreateRBHook        = nullptr;
static CFunctionHook* g_blurFramebufferHook      = nullptr;
static CFunctionHook* g_renderTextureHook        = nullptr;
static CFunctionHook* g_preDrawSurfaceHook       = nullptr;
static CFunctionHook* g_getShaderVariantHook     = nullptr;
static CFunctionHook* g_ensureVRRHook            = nullptr;
static bool           g_disableUnmodifiedCopyMRT = true;
static SP<CShader>     g_captureShader;
static std::unordered_set<uintptr_t> g_scalarAlphaCorrectionTextures;
static std::unordered_set<uintptr_t> g_alphaCorrectionTextures;
static std::unordered_map<Render::ShaderFeatureFlags, SP<CShader>> g_alphaCorrectionSurfaceShaders;
static bool           g_correctSurfaceAlphaShader = false;
static std::unordered_map<uintptr_t, CTimer> g_surfaceDebugTimers;
static constexpr const char*                 SURFACE_DEBUG_LOG = "/tmp/fix-hdr-screenshare-alpha.log";

struct SDMABUFImportKey {
    uintptr_t               buffer = 0;
    int                     width = 0;
    int                     height = 0;
    uint32_t                format = 0;
    uint64_t                modifier = 0;
    int                     planes = 0;
    std::array<uint32_t, 4> offsets = {0};
    std::array<uint32_t, 4> strides = {0};
    std::array<int, 4>      fds = {-1, -1, -1, -1};

    bool operator==(const SDMABUFImportKey& other) const = default;
};

struct SDMABUFImportKeyHash {
    size_t operator()(const SDMABUFImportKey& key) const {
        size_t seed = 0;
        auto   combine = [&](const auto value) {
            seed ^= std::hash<std::decay_t<decltype(value)>>{}(value) + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
        };

        combine(key.buffer);
        combine(key.width);
        combine(key.height);
        combine(key.format);
        combine(key.modifier);
        combine(key.planes);

        for (int i = 0; i < key.planes; ++i) {
            combine(key.offsets[i]);
            combine(key.strides[i]);
            combine(key.fds[i]);
        }

        return seed;
    }
};

static std::unordered_set<SDMABUFImportKey, SDMABUFImportKeyHash> g_importableDMABUFs;
static constexpr size_t                                          MAX_IMPORT_CACHE_SIZE = 512;
static std::unordered_set<uintptr_t>                             g_srgbBlurTextures;

APICALL EXPORT std::string PLUGIN_API_VERSION() {
    return HYPRLAND_API_VERSION;
}

typedef bool (*origNeedsUnmodifiedCopy)(void*);
typedef void (*origSaveBufferForMirror)(void*, const CBox&);
typedef SP<Render::IRenderbuffer> (*origGetOrCreateRenderbuffer)(void*, SP<Aquamarine::IBuffer>, uint32_t);
typedef SP<Render::ITexture> (*origBlurFramebuffer)(void*, SP<Render::IFramebuffer>, float, CRegion*);
typedef void (*origRenderTextureInternal)(void*, SP<Render::ITexture>, const CBox&, const Render::GL::CHyprOpenGLImpl::STextureRenderData&);
typedef void (*origPreDrawSurface)(void*, WP<CSurfacePassElement>, const CRegion&);
typedef WP<CShader> (*origGetShaderVariant)(void*, Render::ePreparedFragmentShader, Render::ShaderFeatureFlags);
typedef void (*origEnsureVRR)(void*, PHLMONITOR);

static constexpr float HDR_ALPHA_CORRECTION_EXPONENT      = 1.5F;

static void scheduleRefreshForAllMonitors() {
    if (!g_pCompositor)
        return;

    if (!State::monitorState())
        return;

    for (const auto& monitor : State::monitorState()->monitors()) {
        if (!monitor)
            continue;

        monitor->m_forceFullFrames = std::max(monitor->m_forceFullFrames, 1);
        monitor->scheduleFrame(Aquamarine::IOutput::AQ_SCHEDULE_RENDER_MONITOR);
    }
}

static bool hkNeedsUnmodifiedCopy(void* thisptr) {
    const auto monitor = static_cast<Monitor::CMonitor*>(thisptr);

    if (g_disableUnmodifiedCopyMRT && monitor && monitor->inHDR())
        return false;

    return ((origNeedsUnmodifiedCopy)g_needsUnmodifiedCopyHook->m_original)(thisptr);
}

static bool drmPropValue(const int fd, const uint32_t obj, const uint32_t type, const uint32_t prop, uint64_t& value) {
    if (fd < 0 || obj == 0 || prop == 0)
        return false;

    const auto props = drmModeObjectGetProperties(fd, obj, type);
    if (!props)
        return false;

    bool found = false;
    for (uint32_t i = 0; i < props->count_props; ++i) {
        if (props->props[i] != prop)
            continue;

        value = props->prop_values[i];
        found = true;
        break;
    }

    drmModeFreeObjectProperties(props);
    return found;
}

static bool connectorHasVrrSupport(Aquamarine::SDRMConnector* connector) {
    if (!connector || !connector->crtc || !connector->backend)
        return false;

    if (!connector->props.values.vrr_capable || !connector->crtc->props.values.vrr_enabled)
        return false;

    uint64_t capable = 0;
    if (!drmPropValue(connector->backend->drmFD(), connector->id, DRM_MODE_OBJECT_CONNECTOR, connector->props.values.vrr_capable, capable))
        return false;

    return capable != 0;
}

static void correctVrrCapabilityCache(Aquamarine::SDRMConnector* connector) {
    if (!connector || connector->canDoVrr || !connectorHasVrrSupport(connector))
        return;

    connector->canDoVrr = true;
    if (connector->output)
        connector->output->vrrCapable = true;

    if (connector->backend)
        connector->backend->log(Aquamarine::AQ_LOG_DEBUG, std::format("[fix-hdr-screenshare] corrected stale VRR capability cache for {}", connector->szName));
}

static void correctMonitorVrrCapabilityCache(PHLMONITOR monitor) {
    if (!monitor || !monitor->m_output)
        return;

    const auto drmOutput = dynamic_cast<Aquamarine::CDRMOutput*>(monitor->m_output.get());
    if (!drmOutput || !drmOutput->connector)
        return;

    correctVrrCapabilityCache(drmOutput->connector.get());
}

static void correctAllMonitorVrrCapabilityCaches() {
    if (!g_pCompositor)
        return;

    if (!State::monitorState())
        return;

    for (const auto& monitor : State::monitorState()->monitors())
        correctMonitorVrrCapabilityCache(monitor);
}

static void hkEnsureVRR(void* thisptr, PHLMONITOR monitor) {
    if (monitor)
        correctMonitorVrrCapabilityCache(monitor);
    else
        correctAllMonitorVrrCapabilityCaches();

    ((origEnsureVRR)g_ensureVRRHook->m_original)(thisptr, monitor);
}

static bool canImportDMABUFForRenderbuffer(const SP<Aquamarine::IBuffer>& buffer) {
    if (!buffer || !Render::GL::g_pHyprOpenGL)
        return false;

    const auto attrs = buffer->dmabuf();
    if (!attrs.success || attrs.size.x <= 0 || attrs.size.y <= 0 || attrs.format == 0 || attrs.planes < 1 || attrs.planes > 4)
        return false;

    for (int i = 0; i < attrs.planes; ++i) {
        if (attrs.fds[i] < 0 || attrs.strides[i] == 0)
            return false;
    }

    const SDMABUFImportKey key = {
        .buffer   = reinterpret_cast<uintptr_t>(buffer.get()),
        .width    = static_cast<int>(attrs.size.x),
        .height   = static_cast<int>(attrs.size.y),
        .format   = attrs.format,
        .modifier = attrs.modifier,
        .planes   = attrs.planes,
        .offsets  = attrs.offsets,
        .strides  = attrs.strides,
        .fds      = attrs.fds,
    };

    if (g_importableDMABUFs.contains(key))
        return true;

    const auto image = Render::GL::g_pHyprOpenGL->createEGLImage(attrs);
    if (image == EGL_NO_IMAGE_KHR)
        return false;

    Render::GL::g_pHyprOpenGL->m_proc.eglDestroyImageKHR(Render::GL::g_pHyprOpenGL->m_eglDisplay, image);

    if (g_importableDMABUFs.size() >= MAX_IMPORT_CACHE_SIZE)
        g_importableDMABUFs.clear();

    g_importableDMABUFs.emplace(key);
    return true;
}

static SP<Render::IRenderbuffer> hkGetOrCreateRenderbuffer(void* thisptr, SP<Aquamarine::IBuffer> buffer, uint32_t fmt) {
    if (!canImportDMABUFForRenderbuffer(buffer))
        return nullptr;

    return ((origGetOrCreateRenderbuffer)g_getOrCreateRBHook->m_original)(thisptr, buffer, fmt);
}

static NColorManagement::PImageDescription captureImageDescription() {
    return NColorManagement::DEFAULT_SRGB_IMAGE_DESCRIPTION;
}

static bool ensureCaptureShader();
static SP<Render::ITexture> renderSDRBlurFromHDRSource(const SP<Render::IFramebuffer>& source, float a, CRegion* originalDamage);

static bool currentMonitorInHDR() {
    const auto monitorRef = g_pHyprRenderer ? g_pHyprRenderer->m_renderData.pMonitor : PHLMONITORREF{};
    const auto monitor    = monitorRef ? monitorRef.lock() : PHLMONITOR{};
    return monitor && monitor->inHDR();
}

static PHLMONITOR currentMonitor() {
    const auto monitorRef = g_pHyprRenderer ? g_pHyprRenderer->m_renderData.pMonitor : PHLMONITORREF{};
    return monitorRef ? monitorRef.lock() : PHLMONITOR{};
}

static float correctHDRAlpha(float alpha) {
    alpha = std::clamp(alpha, 0.0F, 1.0F);
    if (alpha <= 0.0F || alpha >= 1.0F)
        return alpha;

    return 1.0F - std::pow(1.0F - alpha, HDR_ALPHA_CORRECTION_EXPONENT);
}

static void appendSurfaceDebugLog(const std::string& line) {
    FILE* file = std::fopen(SURFACE_DEBUG_LOG, "a");
    if (!file)
        return;

    std::fputs(line.c_str(), file);
    std::fputc('\n', file);
    std::fclose(file);
}

static SP<Render::ITexture> hkBlurFramebuffer(void* thisptr, SP<Render::IFramebuffer> source, float a, CRegion* originalDamage) {
    auto tex = currentMonitorInHDR() ? renderSDRBlurFromHDRSource(source, a, originalDamage) : nullptr;
    if (!tex)
        tex = ((origBlurFramebuffer)g_blurFramebufferHook->m_original)(thisptr, source, a, originalDamage);

    if (currentMonitorInHDR() && tex)
        g_srgbBlurTextures.emplace(reinterpret_cast<uintptr_t>(tex.get()));

    return tex;
}

static void hkPreDrawSurface(void* thisptr, WP<CSurfacePassElement> element, const CRegion& damage) {
    const auto monitor = currentMonitor();
    if (!monitor || !monitor->inHDR() || !element) {
        ((origPreDrawSurface)g_preDrawSurfaceHook->m_original)(thisptr, element, damage);
        return;
    }

    auto surface = Desktop::View::CWLSurface::fromResource(element->m_data.surface);
    const float alphaModifier = surface ? surface->m_alphaModifier : 1.0F;
    const float overallOpacity = surface ? surface->m_overallOpacity : 1.0F;
    const float totalAlpha = element->m_data.alpha * element->m_data.fadeAlpha * alphaModifier * overallOpacity;
    const float correctedTotalAlpha = correctHDRAlpha(totalAlpha);
    const auto  tex = element->m_data.texture;

    if (tex && (totalAlpha < 0.999F || tex->m_type == Render::TEXTURE_RGBA || !tex->m_opaque)) {
        const auto key = reinterpret_cast<uintptr_t>(element->m_data.surface.get());
        auto&      timer = g_surfaceDebugTimers[key];

        if (timer.getSeconds() >= 1.0) {
            timer.reset();
            const auto window = element->m_data.pWindow;
            const auto cls    = window ? window->m_class : std::string{"<no-window>"};
            const auto title  = window ? window->m_title : std::string{"<no-title>"};

            appendSurfaceDebugLog(std::format(
                "class='{}' title='{}' alpha={} fade={} alphaModifier={} overallOpacity={} total={} corrected={} texType={} texOpaque={} surface={:x}",
                cls, title, element->m_data.alpha, element->m_data.fadeAlpha, alphaModifier, overallOpacity, totalAlpha, correctedTotalAlpha, sc<int>(tex->m_type),
                tex->m_opaque, key));
        }
    }

    const bool  correctScalarAlpha  = tex && totalAlpha > 0.0F && totalAlpha < 1.0F;
    const bool  correctTextureAlpha = tex && tex->m_type == Render::TEXTURE_RGBA && !tex->m_opaque && totalAlpha >= 0.999F;
    const auto  textureKey = correctTextureAlpha ? reinterpret_cast<uintptr_t>(tex.get()) : 0;
    const auto  scalarTextureKey = correctScalarAlpha ? reinterpret_cast<uintptr_t>(tex.get()) : 0;

    if (correctScalarAlpha)
        g_scalarAlphaCorrectionTextures.emplace(scalarTextureKey);
    if (correctTextureAlpha)
        g_alphaCorrectionTextures.emplace(textureKey);

    ((origPreDrawSurface)g_preDrawSurfaceHook->m_original)(thisptr, element, damage);

    if (correctTextureAlpha)
        g_alphaCorrectionTextures.erase(textureKey);
    if (correctScalarAlpha)
        g_scalarAlphaCorrectionTextures.erase(scalarTextureKey);
}

static WP<CShader> hkGetShaderVariant(void* thisptr, Render::ePreparedFragmentShader frag, Render::ShaderFeatureFlags features) {
    if (!g_correctSurfaceAlphaShader || frag != Render::SH_FRAG_SURFACE || !(features & Render::SH_FEAT_RGBA) || !Render::g_pShaderLoader ||
        !Render::GL::g_pHyprOpenGL || !Render::GL::g_pHyprOpenGL->m_shaders) {
        return ((origGetShaderVariant)g_getShaderVariantHook->m_original)(thisptr, frag, features);
    }

    if (auto it = g_alphaCorrectionSurfaceShaders.find(features); it != g_alphaCorrectionSurfaceShaders.end())
        return it->second;

    auto source = Render::g_pShaderLoader->getVariantSource(frag, features);

    static constexpr std::string_view NEEDLE = "vec4 pixColor = texture(tex, v_texcoord);";
    const auto                        pos    = source.find(NEEDLE);
    if (pos == std::string::npos)
        return ((origGetShaderVariant)g_getShaderVariantHook->m_original)(thisptr, frag, features);

    const auto replacement = std::format(R"SHADER(vec4 pixColor = texture(tex, v_texcoord);
    if (pixColor.a > 0.0 && pixColor.a < 1.0)
        pixColor.a = 1.0 - pow(1.0 - pixColor.a, {:.8f});)SHADER",
                                         HDR_ALPHA_CORRECTION_EXPONENT);
    source.replace(pos, NEEDLE.size(), replacement);

    auto shader = makeShared<CShader>();
    if (!shader->createProgram(Render::GL::g_pHyprOpenGL->m_shaders->TEXVERTSRC, source, true, true))
        return ((origGetShaderVariant)g_getShaderVariantHook->m_original)(thisptr, frag, features);

    g_alphaCorrectionSurfaceShaders.emplace(features, shader);
    return shader;
}

static void hkRenderTextureInternal(void* thisptr, SP<Render::ITexture> tex, const CBox& box, const Render::GL::CHyprOpenGLImpl::STextureRenderData& data) {
    const auto key          = reinterpret_cast<uintptr_t>(tex.get());
    const auto monitor      = currentMonitor();
    const bool relabelBlur  = monitor && monitor->inHDR() && tex && g_srgbBlurTextures.contains(key);
    const auto originalDesc = relabelBlur ? tex->m_imageDescription : NColorManagement::PImageDescription{};
    const bool correctTextureAlpha = monitor && monitor->inHDR() && !relabelBlur && !data.discardActive && g_alphaCorrectionTextures.contains(key);
    const bool correctScalarAlpha =
        monitor && monitor->inHDR() && !relabelBlur && !data.discardActive && g_scalarAlphaCorrectionTextures.contains(key) && data.a > 0.0F && data.a < 1.0F;
    const bool previousCorrectSurfaceAlphaShader = g_correctSurfaceAlphaShader;
    auto       correctedData = data;

    if (relabelBlur)
        tex->m_imageDescription = NColorManagement::DEFAULT_SRGB_IMAGE_DESCRIPTION;

    if (correctScalarAlpha)
        correctedData.a = correctHDRAlpha(data.a);

    g_correctSurfaceAlphaShader = correctTextureAlpha;
    ((origRenderTextureInternal)g_renderTextureHook->m_original)(thisptr, tex, box, correctedData);
    g_correctSurfaceAlphaShader = previousCorrectSurfaceAlphaShader;

    if (relabelBlur) {
        tex->m_imageDescription = originalDesc;
        g_srgbBlurTextures.erase(key);
    }
}

static bool ensureCaptureShader() {
    if (g_captureShader)
        return true;

    if (!Render::GL::g_pHyprOpenGL || !Render::GL::g_pHyprOpenGL->m_shadersInitialized || !Render::GL::g_pHyprOpenGL->m_shaders)
        return false;

    static const std::string FRAG = R"SHADER(
#version 300 es
precision highp float;
in vec2 v_texcoord;
uniform sampler2D tex;
uniform float sdrMinLuminance;
uniform float sdrMaxLuminance;
uniform float inverseSdrBrightness;
uniform float inverseSdrSaturation;
uniform float contrast;
uniform float brightness;
layout(location = 0) out vec4 fragColor;

const float EXT_LINEAR_MIN_LUMINANCE = 0.0;
const float EXT_LINEAR_MAX_LUMINANCE = 80.0;

vec3 applySaturation(vec3 color, float saturation) {
    float y = dot(color, vec3(0.2126, 0.7152, 0.0722));
    return mix(vec3(y), color, saturation);
}

vec3 gain(vec3 src, float k) {
    vec3 x = clamp(src, 0.0, 1.0);
    vec3 t = step(0.5, x);
    vec3 y = mix(x, 1.0 - x, t);
    vec3 a = 0.5 * pow(2.0 * y, vec3(k));
    return mix(a, 1.0 - a, t);
}

vec3 linearToSrgb(vec3 color) {
    bvec3 cutoff = lessThanEqual(color, vec3(0.0031308));
    vec3  lo     = color * 12.92;
    vec3  hi     = 1.055 * pow(max(color, vec3(0.0)), vec3(1.0 / 2.4)) - 0.055;
    return mix(hi, lo, cutoff);
}

void main() {
    vec4 src = texture(tex, v_texcoord);
    vec3 rgb = max(src.rgb, vec3(0.0));

    rgb *= inverseSdrBrightness;
    rgb = applySaturation(rgb, inverseSdrSaturation);

    rgb = rgb * (EXT_LINEAR_MAX_LUMINANCE - EXT_LINEAR_MIN_LUMINANCE) + vec3(EXT_LINEAR_MIN_LUMINANCE);

    float sdrRange = max(sdrMaxLuminance - sdrMinLuminance, 0.001);
    rgb            = clamp((rgb - vec3(sdrMinLuminance)) / sdrRange, 0.0, 1.0);
    rgb            = linearToSrgb(rgb);

    if (contrast != 1.0)
        rgb = gain(rgb, contrast);
    rgb *= max(1.0, brightness);

    fragColor = vec4(rgb, 1.0);
}
)SHADER";

    g_captureShader = makeShared<CShader>();
    if (!g_captureShader->createProgram(Render::GL::g_pHyprOpenGL->m_shaders->TEXVERTSRC, FRAG, true, true)) {
        g_captureShader.reset();
        return false;
    }

    return true;
}

static bool renderCaptureShader(const SP<Render::ITexture>& sourceTex,
                                const SP<Render::IFramebuffer>& mirrorFB,
                                const CBox& box,
                                const float sdrMinLuminance,
                                const float sdrMaxLuminance,
                                const float inverseSdrBrightness,
                                const float inverseSdrSaturation) {
    if (!g_pHyprRenderer || !Render::GL::g_pHyprOpenGL || !sourceTex || !mirrorFB || !ensureCaptureShader())
        return false;

    auto guard = g_pHyprRenderer->bindTempFB(mirrorFB);
    if (!guard)
        return false;

    Render::GL::g_pHyprOpenGL->blend(false);

    const auto& glMatrix = g_pHyprRenderer->projectBoxToTarget(box);

    glActiveTexture(GL_TEXTURE0);
    sourceTex->bind();
    sourceTex->setTexParameter(GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    sourceTex->setTexParameter(GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    sourceTex->setTexParameter(GL_TEXTURE_MAG_FILTER, sourceTex->magFilter);
    sourceTex->setTexParameter(GL_TEXTURE_MIN_FILTER, sourceTex->minFilter);

    auto shader = Render::GL::g_pHyprOpenGL->useShader(g_captureShader);
    shader->setUniformMatrix3fv(SHADER_PROJ, 1, GL_TRUE, glMatrix.getMatrix());
    shader->setUniformInt(SHADER_TEX, 0);
    glUniform1f(glGetUniformLocation(shader->program(), "sdrMinLuminance"), sdrMinLuminance);
    glUniform1f(glGetUniformLocation(shader->program(), "sdrMaxLuminance"), sdrMaxLuminance);
    glUniform1f(glGetUniformLocation(shader->program(), "inverseSdrBrightness"), inverseSdrBrightness);
    glUniform1f(glGetUniformLocation(shader->program(), "inverseSdrSaturation"), inverseSdrSaturation);
    glUniform1f(glGetUniformLocation(shader->program(), "contrast"), 1.0F);
    glUniform1f(glGetUniformLocation(shader->program(), "brightness"), 1.0F);

    glBindVertexArray(shader->getUniformLocation(SHADER_SHADER_VAO));
    glBindBuffer(GL_ARRAY_BUFFER, shader->getUniformLocation(SHADER_SHADER_VBO));
    glBufferData(GL_ARRAY_BUFFER, sizeof(Render::GL::fullVerts), nullptr, GL_DYNAMIC_DRAW);

    auto verts = Render::GL::fullVerts;
    glBufferSubData(GL_ARRAY_BUFFER, 0, sizeof(verts), verts.data());

    g_pHyprRenderer->m_renderData.finalDamage.forEachRect([](const auto& rect) {
        Render::GL::g_pHyprOpenGL->scissor(&rect, g_pHyprRenderer->m_renderData.transformDamage);
        glDrawArrays(GL_TRIANGLE_STRIP, 0, 4);
    });

    glBindVertexArray(0);
    glBindBuffer(GL_ARRAY_BUFFER, 0);
    sourceTex->unbind();
    Render::GL::g_pHyprOpenGL->scissor(nullptr);
    Render::GL::g_pHyprOpenGL->blend(true);

    return true;
}

static bool renderCaptureShaderToFB(const SP<Render::ITexture>& sourceTex,
                                    const SP<Render::IFramebuffer>& targetFB,
                                    const Mat3x3& matrix,
                                    const CRegion& damage,
                                    const float sdrMinLuminance,
                                    const float sdrMaxLuminance,
                                    const float inverseSdrBrightness,
                                    const float inverseSdrSaturation,
                                    const float contrast,
                                    const float brightness) {
    if (!g_pHyprRenderer || !Render::GL::g_pHyprOpenGL || !sourceTex || !targetFB || !ensureCaptureShader())
        return false;

    auto guard = g_pHyprRenderer->bindTempFB(targetFB);
    if (!guard)
        return false;

    dc<Render::GL::CGLFramebuffer*>(targetFB.get())->clearAfterInvalidation();

    glActiveTexture(GL_TEXTURE0);
    sourceTex->bind();
    sourceTex->setTexParameter(GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    sourceTex->setTexParameter(GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    sourceTex->setTexParameter(GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    sourceTex->setTexParameter(GL_TEXTURE_MIN_FILTER, GL_LINEAR);

    auto shader = Render::GL::g_pHyprOpenGL->useShader(g_captureShader);
    shader->setUniformMatrix3fv(SHADER_PROJ, 1, GL_TRUE, matrix.getMatrix());
    shader->setUniformInt(SHADER_TEX, 0);
    glUniform1f(glGetUniformLocation(shader->program(), "sdrMinLuminance"), sdrMinLuminance);
    glUniform1f(glGetUniformLocation(shader->program(), "sdrMaxLuminance"), sdrMaxLuminance);
    glUniform1f(glGetUniformLocation(shader->program(), "inverseSdrBrightness"), inverseSdrBrightness);
    glUniform1f(glGetUniformLocation(shader->program(), "inverseSdrSaturation"), inverseSdrSaturation);
    glUniform1f(glGetUniformLocation(shader->program(), "contrast"), contrast);
    glUniform1f(glGetUniformLocation(shader->program(), "brightness"), brightness);

    glBindVertexArray(shader->getUniformLocation(SHADER_SHADER_VAO));
    glBindBuffer(GL_ARRAY_BUFFER, shader->getUniformLocation(SHADER_SHADER_VBO));
    glBufferData(GL_ARRAY_BUFFER, sizeof(Render::GL::fullVerts), nullptr, GL_DYNAMIC_DRAW);

    auto verts = Render::GL::fullVerts;
    glBufferSubData(GL_ARRAY_BUFFER, 0, sizeof(verts), verts.data());

    if (!damage.empty()) {
        damage.forEachRect([](const auto& rect) {
            Render::GL::g_pHyprOpenGL->scissor(&rect, false);
            glDrawArrays(GL_TRIANGLE_STRIP, 0, 4);
        });
    }

    glBindVertexArray(0);
    glBindBuffer(GL_ARRAY_BUFFER, 0);
    sourceTex->unbind();
    Render::GL::g_pHyprOpenGL->scissor(nullptr);

    return true;
}

static SP<Render::ITexture> renderSDRBlurFromHDRSource(const SP<Render::IFramebuffer>& source, float a, CRegion* originalDamage) {
    if (!g_pHyprRenderer || !Render::GL::g_pHyprOpenGL || !source || !source->getTexture() || !originalDamage)
        return nullptr;

    const auto monitor = currentMonitor();
    if (!monitor || !monitor->inHDR())
        return nullptr;

    const auto resources = monitor->resources();
    if (!resources)
        return nullptr;

    const auto blurFB     = resources->getUnusedWorkBuffer();
    const auto blurSwapFB = resources->getUnusedWorkBuffer();
    if (!blurFB || !blurSwapFB || blurFB == blurSwapFB)
        return nullptr;

    static auto PBLURSIZE             = CConfigValue<Config::INTEGER>("decoration:blur:size");
    static auto PBLURPASSES           = CConfigValue<Config::INTEGER>("decoration:blur:passes");
    static auto PBLURVIBRANCY         = CConfigValue<Config::FLOAT>("decoration:blur:vibrancy");
    static auto PBLURVIBRANCYDARKNESS = CConfigValue<Config::FLOAT>("decoration:blur:vibrancy_darkness");
    static auto PBLURCONTRAST         = CConfigValue<Config::FLOAT>("decoration:blur:contrast");
    static auto PBLURNOISE            = CConfigValue<Config::FLOAT>("decoration:blur:noise");
    static auto PBLURBRIGHTNESS       = CConfigValue<Config::FLOAT>("decoration:blur:brightness");

    const auto TRANSFORM  = Math::wlTransformToHyprutils(Math::invertTransform(monitor->m_transform));
    CBox       monitorBox = {0, 0, monitor->m_transformedSize.x, monitor->m_transformedSize.y};
    const auto glMatrix   = g_pHyprRenderer->projectBoxToTarget(monitorBox, TRANSFORM);

    const auto blurPasses = std::clamp(*PBLURPASSES, sc<int64_t>(1), sc<int64_t>(8));
    CRegion   damage{*originalDamage};
    damage.transform(TRANSFORM, monitor->m_transformedSize.x, monitor->m_transformedSize.y);
    damage.expand(std::clamp(*PBLURSIZE, sc<int64_t>(1), sc<int64_t>(40)) * std::pow(2, blurPasses));

    const float sdrMaxLuminance = std::max<float>(1.0F, monitor->m_sdrMaxLuminance);
    const float sdrMinLuminance = std::max<float>(0.0F, monitor->m_sdrMinLuminance);
    const float inverseSdrBrightness = monitor->m_sdrBrightness > 0.0F ? 1.0F / monitor->m_sdrBrightness : 1.0F;
    const float inverseSdrSaturation = monitor->m_sdrSaturation > 0.0F ? 1.0F / monitor->m_sdrSaturation : 1.0F;

    const bool blendWasEnabled = glIsEnabled(GL_BLEND);
    Render::GL::g_pHyprOpenGL->blend(false);
    Render::GL::g_pHyprOpenGL->setCapStatus(GL_STENCIL_TEST, false);

    if (!renderCaptureShaderToFB(source->getTexture(), blurSwapFB, glMatrix, damage, sdrMinLuminance, sdrMaxLuminance, inverseSdrBrightness, inverseSdrSaturation,
                                 *PBLURCONTRAST, *PBLURBRIGHTNESS)) {
        Render::GL::g_pHyprOpenGL->blend(blendWasEnabled);
        return nullptr;
    }

    auto currentRenderToFB = blurSwapFB;

    auto drawPass = [&](WP<CShader> shader, Render::ePreparedFragmentShader frag, CRegion* passDamage) {
        if (currentRenderToFB == blurFB)
            blurSwapFB->bind();
        else
            blurFB->bind();

        glActiveTexture(GL_TEXTURE0);
        auto currentTex = currentRenderToFB->getTexture();
        currentTex->bind();
        currentTex->setTexParameter(GL_TEXTURE_MIN_FILTER, GL_LINEAR);

        shader->setUniformMatrix3fv(SHADER_PROJ, 1, GL_TRUE, glMatrix.getMatrix());
        shader->setUniformFloat(SHADER_RADIUS, *PBLURSIZE * a);
        if (frag == Render::SH_FRAG_BLUR1) {
            shader->setUniformFloat2(SHADER_HALFPIXEL, 0.5F / (monitor->m_pixelSize.x / 2.F), 0.5F / (monitor->m_pixelSize.y / 2.F));
            shader->setUniformInt(SHADER_PASSES, blurPasses);
            shader->setUniformFloat(SHADER_VIBRANCY, *PBLURVIBRANCY);
            shader->setUniformFloat(SHADER_VIBRANCY_DARKNESS, *PBLURVIBRANCYDARKNESS);
        } else
            shader->setUniformFloat2(SHADER_HALFPIXEL, 0.5F / (monitor->m_pixelSize.x * 2.F), 0.5F / (monitor->m_pixelSize.y * 2.F));
        shader->setUniformInt(SHADER_TEX, 0);

        glBindVertexArray(shader->getUniformLocation(SHADER_SHADER_VAO));

        if (!passDamage->empty()) {
            passDamage->forEachRect([](const auto& rect) {
                Render::GL::g_pHyprOpenGL->scissor(&rect, false);
                glDrawArrays(GL_TRIANGLE_STRIP, 0, 4);
            });
        }

        glBindVertexArray(0);

        currentRenderToFB = currentRenderToFB == blurFB ? blurSwapFB : blurFB;
    };

    CRegion tempDamage{damage};

    blurFB->bind();
    dc<Render::GL::CGLFramebuffer*>(blurFB.get())->clearAfterInvalidation();

    auto shader = Render::GL::g_pHyprOpenGL->useShader(Render::GL::g_pHyprOpenGL->getShaderVariant(Render::SH_FRAG_BLUR1));
    for (auto i = 1; i <= blurPasses; ++i) {
        tempDamage = damage.copy().scale(1.F / (1 << i));
        drawPass(shader, Render::SH_FRAG_BLUR1, &tempDamage);
    }

    shader = Render::GL::g_pHyprOpenGL->useShader(Render::GL::g_pHyprOpenGL->getShaderVariant(Render::SH_FRAG_BLUR2));
    for (auto i = blurPasses - 1; i >= 0; --i) {
        tempDamage = damage.copy().scale(1.F / (1 << i));
        drawPass(shader, Render::SH_FRAG_BLUR2, &tempDamage);
    }

    if (currentRenderToFB == blurFB)
        blurSwapFB->bind();
    else
        blurFB->bind();

    glActiveTexture(GL_TEXTURE0);
    auto currentTex = currentRenderToFB->getTexture();
    currentTex->bind();
    currentTex->setTexParameter(GL_TEXTURE_MIN_FILTER, GL_LINEAR);

    shader = Render::GL::g_pHyprOpenGL->useShader(Render::GL::g_pHyprOpenGL->getShaderVariant(Render::SH_FRAG_BLURFINISH));
    shader->setUniformMatrix3fv(SHADER_PROJ, 1, GL_TRUE, glMatrix.getMatrix());
    shader->setUniformFloat(SHADER_NOISE, *PBLURNOISE);
    shader->setUniformFloat(SHADER_BRIGHTNESS, *PBLURBRIGHTNESS);
    shader->setUniformInt(SHADER_TEX, 0);

    glBindVertexArray(shader->getUniformLocation(SHADER_SHADER_VAO));
    if (!damage.empty()) {
        damage.forEachRect([](const auto& rect) {
            Render::GL::g_pHyprOpenGL->scissor(&rect, false);
            glDrawArrays(GL_TRIANGLE_STRIP, 0, 4);
        });
    }
    glBindVertexArray(0);

    currentRenderToFB = currentRenderToFB == blurFB ? blurSwapFB : blurFB;
    Render::GL::g_pHyprOpenGL->scissor(nullptr);
    currentTex->unbind();
    Render::GL::g_pHyprOpenGL->blend(blendWasEnabled);

    return currentRenderToFB->getTexture();
}

static void hkSaveBufferForMirror(void* thisptr, const CBox& box) {
    const auto monitorRef = g_pHyprRenderer ? g_pHyprRenderer->m_renderData.pMonitor : PHLMONITORREF{};
    const auto monitor    = monitorRef ? monitorRef.lock() : PHLMONITOR{};

    if (!monitor || !monitor->inHDR()) {
        ((origSaveBufferForMirror)g_saveBufferForMirrorHook->m_original)(thisptr, box);
        return;
    }

    const auto resources = monitor->resources();
    if (!resources || !g_pHyprRenderer || !g_pHyprRenderer->m_renderData.currentFB)
        return;

    const auto sourceTex = resources->m_mirrorTex ? resources->m_mirrorTex : g_pHyprRenderer->m_renderData.currentFB->getTexture();
    const auto mirrorFB  = resources->mirrorFB();
    if (!sourceTex || !mirrorFB)
        return;

    if (mirrorFB)
        mirrorFB->setImageDescription(captureImageDescription());

    const float sdrMaxLuminance = std::max<float>(1.0F, monitor->m_sdrMaxLuminance);
    const float sdrMinLuminance = std::max<float>(0.0F, monitor->m_sdrMinLuminance);
    const float inverseSdrBrightness = monitor && monitor->m_sdrBrightness > 0.0F ? 1.0F / monitor->m_sdrBrightness : 1.0F;
    const float inverseSdrSaturation = monitor && monitor->m_sdrSaturation > 0.0F ? 1.0F / monitor->m_sdrSaturation : 1.0F;

    if (renderCaptureShader(sourceTex, mirrorFB, box, sdrMinLuminance, sdrMaxLuminance, inverseSdrBrightness, inverseSdrSaturation))
        return;
}

static void* findFnOrThrow(const std::string& name, std::initializer_list<std::string_view> demangledNeedles) {
    auto fns = HyprlandAPI::findFunctionsByName(g_pluginHandle, name);
    if (fns.empty())
        throw std::runtime_error(std::format("[fix-hdr-screenshare] No functions found for {}", name));

    if (demangledNeedles.size() == 0 || (demangledNeedles.size() == 1 && demangledNeedles.begin()->empty()))
        return fns[0].address;

    std::vector<SFunctionMatch> matches;
    matches.reserve(fns.size());
    for (const auto& fn : fns) {
        for (const auto& needle : demangledNeedles) {
            if (needle.empty() || fn.demangled.find(needle) != std::string::npos) {
                matches.push_back(fn);
                break;
            }
        }
    }

    if (matches.empty())
        throw std::runtime_error(std::format("[fix-hdr-screenshare] No matching overload for {}", name));

    if (matches.size() > 1)
        throw std::runtime_error(std::format("[fix-hdr-screenshare] Ambiguous overload for {}", name));

    return matches[0].address;
}

APICALL EXPORT PLUGIN_DESCRIPTION_INFO PLUGIN_INIT(HANDLE handle) {
    g_pluginHandle = handle;
    const std::string HASH        = __hyprland_api_get_hash();
    const std::string CLIENT_HASH = __hyprland_api_get_client_hash();

    if (HASH != CLIENT_HASH)
        throw std::runtime_error("Version mismatch: headers version is not equal to running Hyprland version");

    g_disableUnmodifiedCopyMRT = true;
    g_needsUnmodifiedCopyHook  = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("needsUnmodifiedCopy", {"CMonitor::needsUnmodifiedCopy("}),
        (void*)hkNeedsUnmodifiedCopy);

    if (!g_needsUnmodifiedCopyHook || !g_needsUnmodifiedCopyHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook CMonitor::needsUnmodifiedCopy");

    g_saveBufferForMirrorHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("saveBufferForMirror", {"CHyprOpenGLImpl::saveBufferForMirror("}),
        (void*)hkSaveBufferForMirror);

    if (!g_saveBufferForMirrorHook || !g_saveBufferForMirrorHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook CHyprOpenGLImpl::saveBufferForMirror");

    g_getOrCreateRBHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("getOrCreateRenderbuffer", {"Render::IHyprRenderer::getOrCreateRenderbuffer("}),
        (void*)hkGetOrCreateRenderbuffer);

    if (!g_getOrCreateRBHook || !g_getOrCreateRBHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook Render::IHyprRenderer::getOrCreateRenderbuffer");

    g_blurFramebufferHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("blurFramebuffer", {"CHyprGLRenderer::blurFramebuffer("}),
        (void*)hkBlurFramebuffer);

    if (!g_blurFramebufferHook || !g_blurFramebufferHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook CHyprGLRenderer::blurFramebuffer");

    g_renderTextureHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("renderTextureInternal", {"CHyprOpenGLImpl::renderTextureInternal("}),
        (void*)hkRenderTextureInternal);

    if (!g_renderTextureHook || !g_renderTextureHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook CHyprOpenGLImpl::renderTextureInternal");

    g_getShaderVariantHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("getShaderVariant", {"CHyprOpenGLImpl::getShaderVariant("}),
        (void*)hkGetShaderVariant);

    if (!g_getShaderVariantHook || !g_getShaderVariantHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook CHyprOpenGLImpl::getShaderVariant");

    g_preDrawSurfaceHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("preDrawSurface", {"Render::IElementRenderer::preDrawSurface("}),
        (void*)hkPreDrawSurface);

    if (!g_preDrawSurfaceHook || !g_preDrawSurfaceHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook Render::IElementRenderer::preDrawSurface");

    g_ensureVRRHook = HyprlandAPI::createFunctionHook(
        g_pluginHandle,
        findFnOrThrow("ensureVRR", {"Config::CMonitorRuleManager::ensureVRR("}),
        (void*)hkEnsureVRR);

    if (!g_ensureVRRHook || !g_ensureVRRHook->hook())
        throw std::runtime_error("[fix-hdr-screenshare] Failed to hook Config::CMonitorRuleManager::ensureVRR");

    scheduleRefreshForAllMonitors();

    return {"fix-hdr-screenshare", "Disable the HDR unmodified-copy MRT path used for screenshare", "daniel", "0.4"};
}

APICALL EXPORT void PLUGIN_EXIT() {
    g_disableUnmodifiedCopyMRT = false;

    if (g_needsUnmodifiedCopyHook) {
        g_needsUnmodifiedCopyHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_needsUnmodifiedCopyHook);
        g_needsUnmodifiedCopyHook = nullptr;
    }

    if (g_saveBufferForMirrorHook) {
        g_saveBufferForMirrorHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_saveBufferForMirrorHook);
        g_saveBufferForMirrorHook = nullptr;
    }

    if (g_getOrCreateRBHook) {
        g_getOrCreateRBHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_getOrCreateRBHook);
        g_getOrCreateRBHook = nullptr;
    }

    if (g_blurFramebufferHook) {
        g_blurFramebufferHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_blurFramebufferHook);
        g_blurFramebufferHook = nullptr;
    }

    if (g_renderTextureHook) {
        g_renderTextureHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_renderTextureHook);
        g_renderTextureHook = nullptr;
    }

    if (g_preDrawSurfaceHook) {
        g_preDrawSurfaceHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_preDrawSurfaceHook);
        g_preDrawSurfaceHook = nullptr;
    }

    if (g_getShaderVariantHook) {
        g_getShaderVariantHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_getShaderVariantHook);
        g_getShaderVariantHook = nullptr;
    }

    if (g_ensureVRRHook) {
        g_ensureVRRHook->unhook();
        HyprlandAPI::removeFunctionHook(g_pluginHandle, g_ensureVRRHook);
        g_ensureVRRHook = nullptr;
    }

    g_importableDMABUFs.clear();
    g_srgbBlurTextures.clear();
    g_scalarAlphaCorrectionTextures.clear();
    g_alphaCorrectionTextures.clear();
    g_alphaCorrectionSurfaceShaders.clear();
    g_surfaceDebugTimers.clear();
    g_captureShader.reset();
    g_correctSurfaceAlphaShader = false;

    scheduleRefreshForAllMonitors();
}
