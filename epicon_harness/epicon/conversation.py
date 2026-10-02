"""Stateful, cumulative conversation history.

One :class:`Conversation` instance belongs to exactly one test case execution.
It is the only thing that carries context between turns, which is what makes
session isolation cheap to guarantee: the runner builds a fresh instance per
test case and never shares it.

The turn protocol is strictly ordered:

1. :meth:`append_user` records the user prompt,
2. the caller transmits :meth:`messages` and waits for the response,
3. :meth:`append_assistant` records the model output.

:meth:`messages` refuses to hand out a history whose last entry is an assistant
message paired with a pending user turn, and :meth:`append_user` refuses to run
ahead of an unanswered turn, so a dropped response can never silently shift the
alignment of later turns.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field
from typing import Literal

Role = Literal["user", "assistant"]


@dataclass(frozen=True)
class Message:
    role: Role
    content: str
    turn_index: int | None = None

    def to_dict(self) -> dict[str, str]:
        return {"role": self.role, "content": self.content}


@dataclass
class Conversation:
    """Append-only transcript for a single isolated session."""

    system_prompt: str = ""
    _messages: list[Message] = field(default_factory=list, repr=False)

    # -- state ------------------------------------------------------------- #
    @property
    def awaiting_response(self) -> bool:
        return bool(self._messages) and self._messages[-1].role == "user"

    @property
    def turn_count(self) -> int:
        return sum(1 for message in self._messages if message.role == "user")

    def __len__(self) -> int:
        return len(self._messages)

    def __iter__(self) -> Iterator[Message]:
        return iter(self._messages)

    # -- mutation ---------------------------------------------------------- #
    def append_user(self, content: str, turn_index: int | None = None) -> None:
        if self.awaiting_response:
            raise RuntimeError(
                "Cannot append a user turn while the previous turn has no assistant "
                "response; the cumulative history would lose its alignment."
            )
        self._messages.append(Message("user", content, turn_index))

    def append_assistant(self, content: str, turn_index: int | None = None) -> None:
        if not self.awaiting_response:
            raise RuntimeError("Cannot append an assistant response without a preceding user turn.")
        self._messages.append(Message("assistant", content, turn_index))

    def rollback_pending_user(self) -> Message | None:
        """Drop an unanswered user turn, e.g. after an unrecoverable API error.

        Keeps the history consistent so remaining turns either continue from the
        last successful exchange or are marked skipped.
        """
        if self.awaiting_response:
            return self._messages.pop()
        return None

    # -- views ------------------------------------------------------------- #
    def messages(self) -> list[Message]:
        """The cumulative history to transmit, ending with the pending user turn."""
        if not self._messages:
            raise RuntimeError("Nothing to transmit: the conversation is empty.")
        if not self.awaiting_response:
            raise RuntimeError(
                "Nothing to transmit: the last message is an assistant response. "
                "Append the next user turn first."
            )
        return list(self._messages)

    def as_dicts(self) -> list[dict[str, str]]:
        return [message.to_dict() for message in self._messages]

    def transcript(self) -> str:
        """Plain-text rendering, handy for debugging a contaminated session."""
        lines = []
        if self.system_prompt:
            lines.append(f"[system]\n{self.system_prompt}\n")
        for message in self._messages:
            lines.append(f"[{message.role}]\n{message.content}\n")
        return "\n".join(lines)
