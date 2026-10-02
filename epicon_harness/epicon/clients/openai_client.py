"""OpenAI-SDK client, pointed at any OpenAI-compatible ``/chat/completions`` API.

The universal driver of REQ-RUN-007: one class serves OpenAI, Google AI Studio,
DeepSeek and NVIDIA NIM, differing only in the ``base_url`` (and a couple of
parameter quirks) carried by the :class:`~epicon.providers.ProviderSpec`.

Compatibility quirks handled here
---------------------------------
* ``max_tokens`` vs ``max_completion_tokens`` (newer OpenAI models reject the former);
* reasoning models that reject ``temperature`` / ``top_p`` — the offending parameter
  is detected from the 400 response, dropped, and remembered for the rest of the
  session, and is then reported as ``null`` in ``model_metadata``;
* reasoning traces exposed as ``reasoning_content`` (DeepSeek) or ``reasoning``;
* cached-prompt and reasoning token counters, where the provider reports them.
"""

from __future__ import annotations

import re
from collections.abc import Sequence
from typing import Any

from ..conversation import Message
from ..errors import MissingDependency
from ..model_spec import ModelSpec
from ..models import Usage
from .base import ChatResponse, LLMClient

_PARAM_IN_ERROR = re.compile(
    r"(?:parameter|argument|field)[s]?[:\s'\"]+([a-z_][a-z0-9_.]*)", re.IGNORECASE
)
_DROPPABLE = ("temperature", "top_p", "reasoning_effort")

#: Maps request parameter names back to ``model_metadata`` field names.
_METADATA_FIELD = {"temperature": "temperature", "top_p": "top_p"}


class OpenAICompatibleClient(LLMClient):
    """Chat Completions client for every non-Anthropic provider."""

    def _build_client(self, api_key: str) -> Any:
        try:
            import openai
        except ImportError as exc:  # pragma: no cover
            raise MissingDependency("openai", "OpenAI-compatible requests") from exc

        #: Parameters this endpoint rejected earlier in the session.
        self._disabled_params: set[str] = set()
        #: Output-limit parameter name, switched if the endpoint rejects the default.
        self._token_param = self.spec.max_tokens_param

        kwargs: dict[str, Any] = {
            "api_key": api_key,
            "timeout": self.timeout,
            "max_retries": self.max_retries_sdk,
        }
        if self.spec.base_url:
            kwargs["base_url"] = self.spec.base_url
        if self.spec.extra_headers:
            kwargs["default_headers"] = dict(self.spec.extra_headers)
        return openai.OpenAI(**kwargs)

    # -- request construction ---------------------------------------------- #
    def _build_kwargs(
        self, system: str, messages: Sequence[Message], model: ModelSpec
    ) -> dict[str, Any]:
        payload: list[dict[str, str]] = []
        if system.strip():
            payload.append({"role": "system", "content": system})
        payload.extend({"role": message.role, "content": message.content} for message in messages)

        kwargs: dict[str, Any] = {"model": model.model_id, "messages": payload}
        kwargs[self._token_param] = model.token_ceiling
        kwargs.update(self._sampling_params(model))

        if model.stop_sequences:
            kwargs["stop"] = list(model.stop_sequences)
        if model.thinking.enabled and model.thinking.effort:
            kwargs["reasoning_effort"] = model.thinking.effort

        if model.extra_body:
            kwargs["extra_body"] = dict(model.extra_body)

        for name in self._disabled_params:
            kwargs.pop(name, None)
        return kwargs

    def _runtime_unsupported(self, _model: ModelSpec) -> set[str]:
        return {
            _METADATA_FIELD[name]
            for name in self._disabled_params
            if name in _METADATA_FIELD
        }

    # -- request execution -------------------------------------------------- #
    def _invoke(
        self, system: str, messages: Sequence[Message], model: ModelSpec
    ) -> ChatResponse:
        kwargs = self._build_kwargs(system, messages, model)
        try:
            response = self._client.chat.completions.create(**kwargs)
        except Exception as exc:
            adjusted = self._adjust_for_rejected_param(exc, kwargs)
            if adjusted is None:
                raise
            response = self._client.chat.completions.create(**adjusted)
            kwargs = adjusted

        choice = (response.choices or [None])[0]
        message = getattr(choice, "message", None)

        return ChatResponse(
            text=(getattr(message, "content", None) or "").strip(),
            reasoning=_extract_reasoning(message),
            usage=_usage_from_response(response),
            finish_reason=getattr(choice, "finish_reason", None),
            response_id=getattr(response, "id", None),
            request_params=_describe_request(kwargs),
            raw=response,
        )

    def _adjust_for_rejected_param(
        self, exc: BaseException, kwargs: dict[str, Any]
    ) -> dict[str, Any] | None:
        """Drop a parameter the endpoint rejected and return retryable kwargs.

        Returns ``None`` when the error is not a recoverable parameter complaint,
        in which case the caller re-raises and the normal retry policy applies.
        """
        if self._status_code(exc) != 400:
            return None

        message = str(exc)
        candidates = {match.lower() for match in _PARAM_IN_ERROR.findall(message)}
        candidates |= {name for name in _DROPPABLE if name in message}

        adjusted = dict(kwargs)
        changed = False

        # `max_tokens` rejected in favour of `max_completion_tokens`, or vice versa.
        for old, new in (
            ("max_tokens", "max_completion_tokens"),
            ("max_completion_tokens", "max_tokens"),
        ):
            if old in adjusted and new in message:
                adjusted[new] = adjusted.pop(old)
                self._disabled_params.add(old)
                self._token_param = new
                changed = True
                break

        for name in _DROPPABLE:
            if name in candidates and name in adjusted:
                adjusted.pop(name)
                self._disabled_params.add(name)
                changed = True

        return adjusted if changed else None

    # -- error introspection ------------------------------------------------ #
    def _is_retryable(self, exc: BaseException) -> bool:
        if type(exc).__name__ in {
            "RateLimitError",
            "APIConnectionError",
            "APITimeoutError",
            "InternalServerError",
        }:
            return True
        return super()._is_retryable(exc)


def _extract_reasoning(message: Any) -> str | None:
    if message is None:
        return None
    for attribute in ("reasoning_content", "reasoning"):
        value = getattr(message, attribute, None)
        if isinstance(value, str) and value.strip():
            return value
    # Some gateways only expose it in the raw payload.
    extra = getattr(message, "model_extra", None) or {}
    for attribute in ("reasoning_content", "reasoning"):
        value = extra.get(attribute) if isinstance(extra, dict) else None
        if isinstance(value, str) and value.strip():
            return value
    return None


def _usage_from_response(response: Any) -> Usage:
    usage = getattr(response, "usage", None)
    if usage is None:
        return Usage()

    prompt_details = getattr(usage, "prompt_tokens_details", None)
    completion_details = getattr(usage, "completion_tokens_details", None)
    cached = int(getattr(prompt_details, "cached_tokens", 0) or 0)
    # DeepSeek reports cache hits at the top level instead.
    cached = cached or int(getattr(usage, "prompt_cache_hit_tokens", 0) or 0)
    reasoning = int(getattr(completion_details, "reasoning_tokens", 0) or 0)

    prompt_tokens = int(getattr(usage, "prompt_tokens", 0) or 0)
    return Usage(
        # Keep `input_tokens` comparable to Anthropic's: uncached prompt tokens.
        input_tokens=max(prompt_tokens - cached, 0),
        output_tokens=int(getattr(usage, "completion_tokens", 0) or 0),
        cache_read_input_tokens=cached,
        reasoning_tokens=reasoning,
    )


def _describe_request(kwargs: dict[str, Any]) -> dict[str, Any]:
    summary = {key: value for key, value in kwargs.items() if key != "messages"}
    summary["message_count"] = len(kwargs.get("messages") or [])
    return summary
