"""Exception hierarchy for the evaluation pipeline."""

from __future__ import annotations


class EpiconError(Exception):
    """Base class for every error raised by this package."""


class ConfigError(EpiconError):
    """Malformed manifest, runner configuration or provider definition."""


class SchemaError(EpiconError):
    """A JSON document does not match the expected template schema."""

    def __init__(self, message: str, *, source: str | None = None) -> None:
        self.source = source
        super().__init__(f"{source}: {message}" if source else message)


class PathOutsideProject(EpiconError):
    """A data path escaped the project root."""


class CredentialError(EpiconError):
    """A credential is missing from the keyring, or the keyring is unusable."""


class ProviderError(EpiconError):
    """Unknown provider, or a provider used with the wrong SDK."""


class ApiError(EpiconError):
    """A provider API call failed after exhausting the retry policy."""

    def __init__(
        self,
        message: str,
        *,
        provider: str | None = None,
        model: str | None = None,
        status_code: int | None = None,
        attempts: int = 1,
        retryable: bool = False,
    ) -> None:
        self.provider = provider
        self.model = model
        self.status_code = status_code
        self.attempts = attempts
        self.retryable = retryable
        super().__init__(message)


class MissingDependency(EpiconError):
    """An optional dependency required for the requested feature is absent."""

    def __init__(self, package: str, purpose: str) -> None:
        self.package = package
        super().__init__(
            f"'{package}' is required for {purpose}. Install it with: pip install {package}"
        )
