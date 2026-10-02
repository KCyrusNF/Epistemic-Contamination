"""Credential storage backed by the OS keyring.

Design constraint from the project brief: credentials are never read from, or
written to, a ``.env`` file. Secrets live in the platform credential store
(Windows Credential Manager, macOS Keychain, Secret Service on Linux) under the
service name :data:`SERVICE_NAME`, keyed by provider id.

For unattended runs (CI, containers) a process environment variable may be used
instead, but only when ``EPICON_ALLOW_ENV_CREDENTIALS=1`` is set. That is an
in-memory variable supplied by the caller, not a dotfile: :func:`assert_no_dotenv`
actively refuses to start when a ``.env`` is present in the project root, so the
"just drop it in a .env" habit fails loudly instead of silently.
"""

from __future__ import annotations

import os
from typing import Protocol

from . import paths
from .errors import CredentialError, MissingDependency

SERVICE_NAME = "epistemic-contamination"
ALLOW_ENV_FLAG = "EPICON_ALLOW_ENV_CREDENTIALS"


def env_var_for(provider: str) -> str:
    """Environment variable consulted for *provider* when env fallback is on."""
    return f"EPICON_{provider.strip().upper().replace('-', '_')}_API_KEY"


def assert_no_dotenv() -> None:
    """Fail fast if a ``.env`` file exists in the project root.

    The pipeline must not depend on dotfile secrets; a stray ``.env`` usually
    means a key is sitting in plaintext next to the code.
    """
    stray = [
        candidate
        for candidate in (paths.PROJECT_ROOT / ".env", paths.PROJECT_ROOT / ".env.local")
        if candidate.exists()
    ]
    if stray:
        names = ", ".join(path.name for path in stray)
        raise CredentialError(
            f"Found {names} in the project root. This pipeline stores secrets in the OS "
            f"keyring and never parses dotenv files. Move the keys into the keyring with "
            f"'python -m epicon creds set <provider>' and delete the file."
        )


class CredentialStore(Protocol):
    """Minimal surface the API clients depend on."""

    def get(self, provider: str) -> str: ...

    def has(self, provider: str) -> bool: ...


class KeyringCredentialManager:
    """Reads API keys from the OS keyring, with an opt-in env fallback."""

    def __init__(
        self,
        service_name: str = SERVICE_NAME,
        *,
        allow_env: bool | None = None,
        enforce_no_dotenv: bool = True,
    ) -> None:
        self.service_name = service_name
        self.allow_env = (
            os.environ.get(ALLOW_ENV_FLAG, "").strip().lower() in {"1", "true", "yes"}
            if allow_env is None
            else allow_env
        )
        if enforce_no_dotenv:
            assert_no_dotenv()
        self._cache: dict[str, str] = {}

    # -- backend ----------------------------------------------------------- #
    @staticmethod
    def _keyring():
        try:
            import keyring
        except ImportError as exc:  # pragma: no cover
            raise MissingDependency("keyring", "credential storage") from exc
        return keyring

    # -- reads ------------------------------------------------------------- #
    def get(self, provider: str) -> str:
        provider = provider.strip().lower()
        if provider in self._cache:
            return self._cache[provider]

        secret: str | None = None
        try:
            secret = self._keyring().get_password(self.service_name, provider)
        except MissingDependency:
            if not self.allow_env:
                raise
        except Exception as exc:  # keyring backend unavailable / locked
            if not self.allow_env:
                raise CredentialError(
                    f"Keyring backend unavailable while reading '{provider}': {exc}"
                ) from exc

        if not secret and self.allow_env:
            secret = os.environ.get(env_var_for(provider))

        if not secret:
            hint = f" or ${env_var_for(provider)}" if self.allow_env else ""
            raise CredentialError(
                f"No API key stored for provider '{provider}'. Add one with:\n"
                f"    python -m epicon creds set {provider}{hint}"
            )

        secret = secret.strip()
        self._cache[provider] = secret
        return secret

    def has(self, provider: str) -> bool:
        try:
            self.get(provider)
        except (CredentialError, MissingDependency):
            return False
        return True

    # -- writes ------------------------------------------------------------ #
    def set(self, provider: str, secret: str) -> None:
        provider = provider.strip().lower()
        secret = secret.strip()
        if not secret:
            raise CredentialError("Refusing to store an empty API key.")
        self._keyring().set_password(self.service_name, provider, secret)
        self._cache[provider] = secret

    def delete(self, provider: str) -> None:
        provider = provider.strip().lower()
        self._cache.pop(provider, None)
        try:
            self._keyring().delete_password(self.service_name, provider)
        except Exception as exc:
            raise CredentialError(f"Could not delete key for '{provider}': {exc}") from exc

    def clear_cache(self) -> None:
        self._cache.clear()


class StaticCredentialStore:
    """In-memory store for tests and dry runs."""

    def __init__(self, keys: dict[str, str] | None = None) -> None:
        self._keys = {k.strip().lower(): v for k, v in (keys or {}).items()}

    def get(self, provider: str) -> str:
        provider = provider.strip().lower()
        try:
            return self._keys[provider]
        except KeyError as exc:
            raise CredentialError(f"No API key configured for '{provider}'.") from exc

    def has(self, provider: str) -> bool:
        return provider.strip().lower() in self._keys
