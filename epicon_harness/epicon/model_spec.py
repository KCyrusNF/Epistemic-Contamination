"""Runtime request configuration.

A test case says *what* to ask; a :class:`ModelSpec` says *who* answers. It comes
from a manifest's ``model`` block or from CLI flags, never from the test case, and
it is the source of the run log's ``model_metadata``.

The hyperparameters are not free: SRS REQ-RUN-009 and NFR-DAT-002 pin
``temperature = 0.0`` on every payload, and REQ-RUN-010 fixes the completion
ceiling at 512 tokens for standard endpoints or 2048 for explicit thinking models
(with a 1024-token reasoning budget). Those values are therefore enforced here
rather than left to the caller, and a non-zero temperature is refused outright:
a run that sampled stochastically is not a valid observation.
"""

from __future__ import annotations

import re
from collections.abc import Mapping
from dataclasses import dataclass, field, replace
from typing import Any

from .errors import ConfigError

#: REQ-RUN-009 / NFR-DAT-002: greedy decoding, pinned across all providers.
PINNED_TEMPERATURE = 0.0
#: REQ-RUN-010: completion ceiling for standard, non-thinking endpoints.
STANDARD_MAX_TOKENS = 512
#: REQ-RUN-010: raised ceiling so generations are not truncated inside <think>.
THINKING_MAX_TOKENS = 2048
#: REQ-RUN-010: explicit reasoning token budget for thinking models.
DEFAULT_THINKING_BUDGET = 1024

_ALNUM_RUN = re.compile(r"[A-Za-z]+|[0-9]+")
_TOKEN = re.compile(r"[A-Za-z0-9]+")


def sanitise_model_id(model_id: str) -> str:
    """Derive the ``SanitizedModelID`` used in SRS REQ-RUN-013 file names.

    The specification gives two worked examples — ``GPT-6-Astra`` → ``GPT6`` and
    ``Claude-4.6-Opus`` → ``Claude46`` — from which the rule is: keep the leading
    alphabetic word plus the version digits that follow it, and drop the trailing
    marketing name. A version segment may carry a ``V`` prefix
    (``DeepSeek-V3.2-Thinking`` → ``DeepSeekV32``).

    The result is a heuristic, so a manifest can override it with
    ``model_short_id`` when a provider's naming defeats the pattern.
    """
    tokens = _TOKEN.findall(model_id or "")
    if not tokens:
        return "model"

    parts = [tokens[0]]
    for token in tokens[1:]:
        if token.isdigit():
            parts.append(token)
            continue
        # A `V3`-style version marker: keep it, then keep collecting its digits.
        if len(token) > 1 and token[0].upper() == "V" and token[1:].isdigit():
            parts.append(token[0].upper() + token[1:])
            continue
        break
    return "".join(parts)


@dataclass(frozen=True)
class ThinkingConfig:
    """Extended thinking (Anthropic) / reasoning effort (OpenAI-compatible)."""

    enabled: bool = False
    budget_tokens: int | None = None
    effort: str | None = None  # "low" | "medium" | "high"

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None) -> ThinkingConfig:
        if not data:
            return cls()
        enabled = bool(data.get("enabled", False))
        budget = data.get("budget_tokens")
        return cls(
            enabled=enabled,
            # REQ-RUN-010: a thinking model without an explicit budget gets the
            # specified default rather than the provider's unbounded behaviour.
            budget_tokens=int(budget) if budget else (DEFAULT_THINKING_BUDGET if enabled else None),
            effort=data.get("effort"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "enabled": self.enabled,
            "budget_tokens": self.budget_tokens,
            "effort": self.effort,
        }


@dataclass(frozen=True)
class ModelSpec:
    """One model at one provider, with the parameters to request."""

    provider: str
    model_id: str
    #: Overrides the derived SanitizedModelID in the output file name.
    model_short_id: str | None = None
    top_p: float | None = None
    max_tokens: int | None = None
    stop_sequences: list[str] = field(default_factory=list)
    thinking: ThinkingConfig = field(default_factory=ThinkingConfig)
    extra_body: dict[str, Any] = field(default_factory=dict)
    #: Overrides the endpoint recorded in ``model_metadata.api_endpoint``.
    api_endpoint: str | None = None
    #: REQ-RUN-011: ephemeral cache breakpoint on the Turn 0 system prompt.
    cache_system_prompt: bool = True
    cache_conversation_prefix: bool = True

    @property
    def temperature(self) -> float:
        """Always 0.0 — greedy decoding is not configurable (REQ-RUN-009)."""
        return PINNED_TEMPERATURE

    @property
    def token_ceiling(self) -> int:
        """The transmitted ``max_tokens`` (REQ-RUN-010)."""
        if self.max_tokens is not None:
            return self.max_tokens
        return THINKING_MAX_TOKENS if self.thinking.enabled else STANDARD_MAX_TOKENS

    @property
    def thinking_budget(self) -> int | None:
        return self.thinking.budget_tokens if self.thinking.enabled else None

    @property
    def sanitised_id(self) -> str:
        return self.model_short_id or sanitise_model_id(self.model_id)

    @property
    def model_name(self) -> str:
        """Alias of ``model_id`` used by older call sites and CLI flags."""
        return self.model_id

    @property
    def label(self) -> str:
        return f"{self.provider}/{self.model_id}"

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str = "<model>") -> ModelSpec:
        if not isinstance(data, Mapping):
            raise ConfigError(f"{source}: 'model' must be a JSON object")

        provider = str(data.get("provider") or "").strip().lower()
        # `model_id` matches the run log schema; `model`/`model_name` are synonyms.
        model_id = str(
            data.get("model_id") or data.get("model_name") or data.get("model") or ""
        ).strip()
        if not provider or not model_id:
            raise ConfigError(
                f"{source}: 'provider' and 'model_id' are required "
                f"(got provider={provider!r}, model_id={model_id!r})"
            )

        _reject_sampling_overrides(data, source)

        max_tokens = data.get("max_tokens") or data.get("max_output_tokens")
        return cls(
            provider=provider,
            model_id=model_id,
            model_short_id=(str(data["model_short_id"]) if data.get("model_short_id") else None),
            top_p=_as_float(data.get("top_p")),
            max_tokens=int(max_tokens) if max_tokens else None,
            stop_sequences=[str(item) for item in (data.get("stop_sequences") or [])],
            thinking=ThinkingConfig.from_dict(data.get("thinking")),
            extra_body=dict(data.get("extra_body") or {}),
            api_endpoint=data.get("api_endpoint"),
            cache_system_prompt=bool(data.get("cache_system_prompt", True)),
            cache_conversation_prefix=bool(data.get("cache_conversation_prefix", True)),
        )

    def merged_with(self, overrides: Mapping[str, Any] | None) -> ModelSpec:
        """Apply a partial override (CLI flags, manifest overrides)."""
        if not overrides:
            return self
        _reject_sampling_overrides(overrides, "<override>")

        patch: dict[str, Any] = {}
        for key in (
            "model_short_id",
            "top_p",
            "max_tokens",
            "api_endpoint",
            "cache_system_prompt",
            "cache_conversation_prefix",
        ):
            if overrides.get(key) is not None:
                patch[key] = overrides[key]
        if overrides.get("provider"):
            patch["provider"] = str(overrides["provider"]).strip().lower()
        for key in ("model_id", "model_name", "model"):
            if overrides.get(key):
                patch["model_id"] = str(overrides[key]).strip()
        if overrides.get("stop_sequences") is not None:
            patch["stop_sequences"] = [str(item) for item in overrides["stop_sequences"]]
        if overrides.get("thinking") is not None:
            patch["thinking"] = ThinkingConfig.from_dict(overrides["thinking"])
        if overrides.get("extra_body"):
            patch["extra_body"] = {**self.extra_body, **overrides["extra_body"]}
        if "max_tokens" in patch:
            patch["max_tokens"] = int(patch["max_tokens"])
        return replace(self, **patch)

    def to_dict(self) -> dict[str, Any]:
        return {
            "provider": self.provider,
            "model_id": self.model_id,
            "model_short_id": self.sanitised_id,
            "temperature": self.temperature,
            "top_p": self.top_p,
            "max_tokens": self.token_ceiling,
            "thinking": self.thinking.to_dict(),
            "stop_sequences": list(self.stop_sequences),
            "extra_body": dict(self.extra_body),
            "api_endpoint": self.api_endpoint,
            "cache_system_prompt": self.cache_system_prompt,
            "cache_conversation_prefix": self.cache_conversation_prefix,
        }


def _reject_sampling_overrides(data: Mapping[str, Any], source: str) -> None:
    """Refuse configuration that would break deterministic reproducibility."""
    temperature = data.get("temperature")
    if temperature is not None and float(temperature) != PINNED_TEMPERATURE:
        raise ConfigError(
            f"{source}: temperature is pinned to {PINNED_TEMPERATURE} by REQ-RUN-009 "
            f"(got {temperature}). A run that sampled stochastically is invalid under "
            f"NFR-DAT-002, so it cannot be configured."
        )
    for key in ("top_k", "random_seed", "seed"):
        if data.get(key) is not None:
            raise ConfigError(
                f"{source}: '{key}' is not transmitted. Decoding is greedy and the run "
                f"log schema has no field for it."
            )


def _as_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None
