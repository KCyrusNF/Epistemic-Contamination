"""Client construction: pick the SDK from the provider spec."""

from __future__ import annotations

from ..credentials import CredentialStore
from ..errors import ProviderError
from ..providers import SDK_ANTHROPIC, SDK_OPENAI, ProviderSpec, get_provider
from .anthropic_client import AnthropicClient
from .base import LLMClient, RetryPolicy
from .openai_client import OpenAICompatibleClient


class ClientFactory:
    """Builds a *fresh* client per test case execution.

    Clients are never pooled across test cases. An ``OpenAI``/``Anthropic``
    instance is cheap, and a per-session instance keeps the adaptive
    parameter-compatibility state (see :class:`OpenAICompatibleClient`) from
    leaking between sessions.
    """

    def __init__(
        self,
        credentials: CredentialStore,
        *,
        retry: RetryPolicy | None = None,
        timeout: float = 600.0,
    ) -> None:
        self.credentials = credentials
        self.retry = retry or RetryPolicy()
        self.timeout = timeout

    def spec_for(self, provider: str) -> ProviderSpec:
        return get_provider(provider)

    def create(self, provider: str, **kwargs: object) -> LLMClient:
        spec = self.spec_for(provider)
        api_key = self.credentials.get(spec.id)

        if spec.sdk == SDK_ANTHROPIC:
            client_cls: type[LLMClient] = AnthropicClient
        elif spec.sdk == SDK_OPENAI:
            client_cls = OpenAICompatibleClient
        else:  # pragma: no cover - guarded at registration time
            raise ProviderError(f"Provider '{spec.id}' declares an unknown sdk '{spec.sdk}'.")

        return client_cls(  # type: ignore[call-arg]
            spec,
            api_key,
            retry=self.retry,
            timeout=self.timeout,
            **kwargs,
        )
