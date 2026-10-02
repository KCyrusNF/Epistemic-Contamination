"""Native Anthropic Messages API client.

Claude is intentionally *not* routed through an OpenAI-compatible shim: the
Messages API is used directly so that

* ``cache_control`` breakpoints (prompt caching) are transmitted verbatim,
* ``cache_creation_input_tokens`` / ``cache_read_input_tokens`` are recorded, and
* extended thinking blocks come back structured instead of inlined.

Cache breakpoint placement
--------------------------
The system instruction — the long, stable part of these test cases — gets one
breakpoint. Within the history, breakpoints are placed on the most recent
assistant messages, which makes turn *n+1* a cache read of the whole turn-*n*
prefix. Anthropic allows at most four breakpoints, so at most two are used for
history.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

from ..conversation import Message
from ..errors import MissingDependency
from ..model_spec import STANDARD_MAX_TOKENS, ModelSpec
from ..models import Usage
from .base import ChatResponse, LLMClient

#: Anthropic permits 4 cache breakpoints per request; keep one for the system prompt.
MAX_HISTORY_BREAKPOINTS = 2

CACHE_CONTROL: dict[str, str] = {"type": "ephemeral"}


class AnthropicClient(LLMClient):
    """Thin wrapper over ``anthropic.Anthropic().messages.create``."""

    def _build_client(self, api_key: str) -> Any:
        try:
            import anthropic
        except ImportError as exc:  # pragma: no cover
            raise MissingDependency("anthropic", "Claude requests") from exc

        kwargs: dict[str, Any] = {
            "api_key": api_key,
            "timeout": self.timeout,
            "max_retries": self.max_retries_sdk,
        }
        if self.spec.base_url:
            kwargs["base_url"] = self.spec.base_url
        if self.spec.extra_headers:
            kwargs["default_headers"] = dict(self.spec.extra_headers)
        return anthropic.Anthropic(**kwargs)

    # -- request construction ---------------------------------------------- #
    def _build_system(self, system: str, cache_system: bool) -> list[dict[str, Any]] | None:
        if not system.strip():
            return None
        block: dict[str, Any] = {"type": "text", "text": system}
        if cache_system and self.spec.supports_cache_control:
            block["cache_control"] = dict(CACHE_CONTROL)
        return [block]

    def _build_messages(
        self, messages: Sequence[Message], cache_prefix: bool
    ) -> list[dict[str, Any]]:
        payload = [
            {
                "role": message.role,
                "content": [{"type": "text", "text": message.content}],
            }
            for message in messages
        ]
        if cache_prefix and self.spec.supports_cache_control:
            self._apply_cache_breakpoints(payload)
        return payload

    @staticmethod
    def _apply_cache_breakpoints(payload: list[dict[str, Any]]) -> None:
        """Mark the trailing assistant turns as cacheable prefixes."""
        assistant_positions = [
            index for index, message in enumerate(payload) if message["role"] == "assistant"
        ]
        for index in assistant_positions[-MAX_HISTORY_BREAKPOINTS:]:
            payload[index]["content"][-1]["cache_control"] = dict(CACHE_CONTROL)

    def _build_kwargs(
        self, system: str, messages: Sequence[Message], model: ModelSpec
    ) -> dict[str, Any]:
        ceiling = model.token_ceiling
        kwargs: dict[str, Any] = {
            "model": model.model_id,
            "max_tokens": ceiling,
            "messages": self._build_messages(messages, model.cache_conversation_prefix),
        }

        system_blocks = self._build_system(system, model.cache_system_prompt)
        if system_blocks:
            kwargs["system"] = system_blocks
        if model.stop_sequences:
            kwargs["stop_sequences"] = list(model.stop_sequences)

        if model.thinking.enabled:
            budget = int(model.thinking_budget or ceiling // 2)
            # The budget is drawn from max_tokens, so leave room for the answer.
            if budget >= ceiling:
                kwargs["max_tokens"] = budget + STANDARD_MAX_TOKENS
            kwargs["thinking"] = {"type": "enabled", "budget_tokens": budget}
            # Extended thinking rejects an explicit temperature, so the value pinned
            # by REQ-RUN-009 cannot be transmitted here. It is reported as null
            # rather than claimed; see _runtime_unsupported below.
        else:
            kwargs.update(self._sampling_params(model))

        if model.extra_body:
            kwargs.update(model.extra_body)
        return kwargs

    def _runtime_unsupported(self, model: ModelSpec) -> set[str]:
        if model.thinking.enabled:
            return {"temperature", "top_p"}
        return set()

    # -- request execution -------------------------------------------------- #
    def _invoke(
        self, system: str, messages: Sequence[Message], model: ModelSpec
    ) -> ChatResponse:
        kwargs = self._build_kwargs(system, messages, model)
        response = self._client.messages.create(**kwargs)

        text_parts: list[str] = []
        thinking_parts: list[str] = []
        for block in response.content or []:
            block_type = getattr(block, "type", None)
            if block_type == "text":
                text_parts.append(getattr(block, "text", "") or "")
            elif block_type in ("thinking", "redacted_thinking"):
                thinking_parts.append(getattr(block, "thinking", "") or "")

        return ChatResponse(
            text="".join(text_parts).strip(),
            reasoning="\n".join(part for part in thinking_parts if part) or None,
            usage=_usage_from_response(response),
            finish_reason=getattr(response, "stop_reason", None),
            response_id=getattr(response, "id", None),
            request_params=_describe_request(kwargs),
            raw=response,
        )

    # -- error introspection ------------------------------------------------ #
    def _is_retryable(self, exc: BaseException) -> bool:
        overloaded = type(exc).__name__ in {
            "InternalServerError",
            "APIConnectionError",
            "APITimeoutError",
            "RateLimitError",
            "OverloadedError",
        }
        return overloaded or super()._is_retryable(exc)


def _usage_from_response(response: Any) -> Usage:
    usage = getattr(response, "usage", None)
    if usage is None:
        return Usage()
    return Usage(
        input_tokens=int(getattr(usage, "input_tokens", 0) or 0),
        output_tokens=int(getattr(usage, "output_tokens", 0) or 0),
        cache_creation_input_tokens=int(getattr(usage, "cache_creation_input_tokens", 0) or 0),
        cache_read_input_tokens=int(getattr(usage, "cache_read_input_tokens", 0) or 0),
    )


def _describe_request(kwargs: dict[str, Any]) -> dict[str, Any]:
    """Log-friendly summary of the request: parameters without the prompt bodies."""
    system_blocks = kwargs.get("system") or []
    messages = kwargs.get("messages") or []
    cached_history = sum(
        1
        for message in messages
        for block in message.get("content", [])
        if isinstance(block, dict) and "cache_control" in block
    )
    summary = {key: value for key, value in kwargs.items() if key not in ("messages", "system")}
    summary["message_count"] = len(messages)
    summary["system_cached"] = any(
        isinstance(block, dict) and "cache_control" in block for block in system_blocks
    )
    summary["history_cache_breakpoints"] = cached_history
    return summary
