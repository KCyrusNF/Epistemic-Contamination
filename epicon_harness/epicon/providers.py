"""Provider registry: which SDK talks to whom, and over which base URL.

Claude is reached through the native ``anthropic`` SDK (Messages API) so that
prompt-caching ``cache_control`` blocks, extended thinking and the cache usage
counters survive intact. Everything else is reached through the ``openai`` SDK
pointed at the provider's OpenAI-compatible ``/chat/completions`` endpoint.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field, replace
from typing import Any

from .errors import ProviderError

SDK_ANTHROPIC = "anthropic"
SDK_OPENAI = "openai"


@dataclass(frozen=True)
class ProviderSpec:
    """Static routing facts for one provider."""

    id: str
    label: str
    sdk: str
    base_url: str | None = None
    api_flavour: str = "chat.completions"
    #: Name of the output-token parameter (`max_tokens` vs `max_completion_tokens`).
    max_tokens_param: str = "max_tokens"
    #: Native prompt caching via explicit cache breakpoints.
    supports_cache_control: bool = False
    #: Parameters this provider is known to reject; dropped before the request.
    unsupported_params: frozenset[str] = frozenset()
    #: Default requests-per-minute budget used by the throttle.
    default_rpm: int = 60
    #: Default number of concurrent in-flight requests.
    default_concurrency: int = 2
    extra_headers: Mapping[str, str] = field(default_factory=dict)

    @property
    def is_anthropic(self) -> bool:
        return self.sdk == SDK_ANTHROPIC


_REGISTRY: dict[str, ProviderSpec] = {
    "anthropic": ProviderSpec(
        id="anthropic",
        label="Anthropic (Claude)",
        sdk=SDK_ANTHROPIC,
        base_url=None,  # SDK default: https://api.anthropic.com
        api_flavour="messages",
        supports_cache_control=True,
        default_rpm=50,
        default_concurrency=2,
    ),
    "openai": ProviderSpec(
        id="openai",
        label="OpenAI",
        sdk=SDK_OPENAI,
        base_url="https://api.openai.com/v1",
        max_tokens_param="max_completion_tokens",
        default_rpm=200,
        default_concurrency=4,
    ),
    "google": ProviderSpec(
        id="google",
        label="Google AI Studio (Gemini)",
        sdk=SDK_OPENAI,
        base_url="https://generativelanguage.googleapis.com/v1beta/openai/",
        default_rpm=60,
        default_concurrency=2,
    ),
    "deepseek": ProviderSpec(
        id="deepseek",
        label="DeepSeek",
        sdk=SDK_OPENAI,
        base_url="https://api.deepseek.com/v1",
        default_rpm=60,
        default_concurrency=3,
    ),
    "nvidia": ProviderSpec(
        id="nvidia",
        label="NVIDIA NIM",
        sdk=SDK_OPENAI,
        base_url="https://integrate.api.nvidia.com/v1",
        default_rpm=60,
        default_concurrency=2,
    ),
    "zai": ProviderSpec(
        id="zai",
        label="Z.ai (GLM)",
        sdk=SDK_OPENAI,
        base_url="https://api.z.ai/api/paas/v4",
        default_rpm=60,
        default_concurrency=2,
    ),
}

#: SRS 3.2 restricts ``model_metadata.provider`` to these five. ``zai`` remains
#: routable for exploratory runs but is outside the specified enumeration.
SRS_PROVIDERS = ("openai", "anthropic", "google", "deepseek", "nvidia")

#: Convenience aliases so test cases can spell providers the obvious way.
_ALIASES = {
    "claude": "anthropic",
    "gemini": "google",
    "google-ai-studio": "google",
    "googleai": "google",
    "z.ai": "zai",
    "z-ai": "zai",
    "zhipu": "zai",
    "glm": "zai",
    "oai": "openai",
    "nim": "nvidia",
    "nvidia-nim": "nvidia",
}


def normalise(provider: str) -> str:
    key = (provider or "").strip().lower()
    return _ALIASES.get(key, key)


def get_provider(provider: str) -> ProviderSpec:
    key = normalise(provider)
    try:
        return _REGISTRY[key]
    except KeyError as exc:
        known = ", ".join(sorted(_REGISTRY))
        raise ProviderError(f"Unknown provider '{provider}'. Known providers: {known}") from exc


def all_providers() -> list[ProviderSpec]:
    return [_REGISTRY[key] for key in sorted(_REGISTRY)]


def register_provider(spec: ProviderSpec, *, overwrite: bool = False) -> None:
    """Add a provider at runtime (e.g. a self-hosted OpenAI-compatible gateway)."""
    key = normalise(spec.id)
    if key in _REGISTRY and not overwrite:
        raise ProviderError(f"Provider '{key}' is already registered.")
    _REGISTRY[key] = replace(spec, id=key)


def register_from_dict(data: Mapping[str, Any], *, overwrite: bool = False) -> ProviderSpec:
    """Register a provider from a manifest's ``providers`` block."""
    provider_id = str(data.get("id") or "").strip().lower()
    if not provider_id:
        raise ProviderError("A custom provider needs an 'id'.")
    sdk = str(data.get("sdk") or SDK_OPENAI).strip().lower()
    if sdk not in (SDK_ANTHROPIC, SDK_OPENAI):
        raise ProviderError(f"Provider '{provider_id}': sdk must be 'anthropic' or 'openai'.")
    if sdk == SDK_OPENAI and not data.get("base_url"):
        raise ProviderError(f"Provider '{provider_id}': 'base_url' is required for the openai SDK.")

    spec = ProviderSpec(
        id=provider_id,
        label=str(data.get("label") or provider_id),
        sdk=sdk,
        base_url=data.get("base_url"),
        api_flavour="messages" if sdk == SDK_ANTHROPIC else "chat.completions",
        max_tokens_param=str(data.get("max_tokens_param") or "max_tokens"),
        supports_cache_control=bool(
            data.get("supports_cache_control", sdk == SDK_ANTHROPIC)
        ),
        unsupported_params=frozenset(data.get("unsupported_params") or ()),
        default_rpm=int(data.get("rpm") or 60),
        default_concurrency=int(data.get("concurrency") or 2),
        extra_headers=dict(data.get("extra_headers") or {}),
    )
    register_provider(spec, overwrite=overwrite)
    return spec
