"""Resource throttling: per-provider rate limits and concurrency caps.

Two independent budgets are enforced per provider:

* a token bucket sized in requests-per-minute, and
* a semaphore capping simultaneous in-flight requests.

Both are process-wide and thread-safe, so multiple worker threads running
different test cases against the same provider share one budget while test cases
against different providers never block each other.
"""

from __future__ import annotations

import threading
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass

from . import providers


class TokenBucket:
    """Classic token bucket: *rate* tokens per *per* seconds, burst = capacity."""

    def __init__(self, rate: float, per: float = 60.0, capacity: float | None = None) -> None:
        if rate <= 0:
            raise ValueError("rate must be positive")
        self.rate = rate / per
        self.capacity = float(capacity if capacity is not None else max(1.0, rate))
        self._tokens = self.capacity
        self._updated = time.monotonic()
        self._lock = threading.Lock()

    def acquire(self, tokens: float = 1.0, timeout: float | None = None) -> float:
        """Block until *tokens* are available. Returns the time spent waiting."""
        deadline = None if timeout is None else time.monotonic() + timeout
        waited = 0.0
        while True:
            with self._lock:
                now = time.monotonic()
                self._tokens = min(
                    self.capacity, self._tokens + (now - self._updated) * self.rate
                )
                self._updated = now
                if self._tokens >= tokens:
                    self._tokens -= tokens
                    return waited
                shortfall = tokens - self._tokens
                sleep_for = shortfall / self.rate

            if deadline is not None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise TimeoutError("Timed out waiting for rate-limit tokens.")
                sleep_for = min(sleep_for, remaining)

            sleep_for = min(max(sleep_for, 0.01), 5.0)
            time.sleep(sleep_for)
            waited += sleep_for


@dataclass(frozen=True)
class ThrottleSettings:
    """Per-provider budget. ``None`` means "use the provider default"."""

    rpm: int | None = None
    concurrency: int | None = None


class ProviderThrottle:
    """Lazily-created buckets and semaphores, one pair per provider."""

    def __init__(
        self,
        settings: dict[str, ThrottleSettings] | None = None,
        default: ThrottleSettings | None = None,
    ) -> None:
        self._settings = {
            providers.normalise(key): value for key, value in (settings or {}).items()
        }
        self._default = default or ThrottleSettings()
        self._buckets: dict[str, TokenBucket] = {}
        self._semaphores: dict[str, threading.BoundedSemaphore] = {}
        self._lock = threading.Lock()

    def _budget(self, provider: str) -> tuple[int, int]:
        spec = providers.get_provider(provider)
        override = self._settings.get(providers.normalise(provider), ThrottleSettings())
        rpm = override.rpm or self._default.rpm or spec.default_rpm
        concurrency = (
            override.concurrency or self._default.concurrency or spec.default_concurrency
        )
        return max(1, int(rpm)), max(1, int(concurrency))

    def _resources(self, provider: str) -> tuple[TokenBucket, threading.BoundedSemaphore]:
        key = providers.normalise(provider)
        with self._lock:
            if key not in self._buckets:
                rpm, concurrency = self._budget(key)
                self._buckets[key] = TokenBucket(rate=rpm, per=60.0)
                self._semaphores[key] = threading.BoundedSemaphore(concurrency)
            return self._buckets[key], self._semaphores[key]

    @contextmanager
    def slot(self, provider: str) -> Iterator[float]:
        """Hold a concurrency slot and a rate-limit token for one request."""
        bucket, semaphore = self._resources(provider)
        semaphore.acquire()
        try:
            waited = bucket.acquire()
            yield waited
        finally:
            semaphore.release()

    def describe(self) -> dict[str, dict[str, int]]:
        """Effective budgets, for logging at startup."""
        known = set(self._settings) | set(self._buckets)
        result: dict[str, dict[str, int]] = {}
        for provider in sorted(known):
            rpm, concurrency = self._budget(provider)
            result[provider] = {"rpm": rpm, "concurrency": concurrency}
        return result
