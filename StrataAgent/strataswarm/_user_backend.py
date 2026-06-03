"""UserBackend: a virtual backend that represents the human user.

Instead of calling an LLM, it:
- Receives messages from other agents (via the swarm's messaging system)
- Detects [BLOCKED_ON_USER] prefix → emits blocking event, pauses nudge monitor
- Waits for user input (from UI/Slack/etc) via inject_user_input()
- On user response → emits unblock event, resumes nudge monitor

This allows "user" to be a real agent in the swarm topology with a proper
lifecycle, while the actual "thinking" is done by the human.
"""

from __future__ import annotations

import asyncio
import logging
from collections.abc import AsyncIterator, Callable, Awaitable
from typing import Any

from ._backend import AgentBackend, BackendConfig, BackendMessage

logger = logging.getLogger("strataswarm.user_backend")

BLOCKED_PREFIX = "[BLOCKED_ON_USER]"


class UserBackend(AgentBackend):
    """Backend that bridges the swarm messaging to a human user.

    The user agent runs a standard SwarmAgent loop with this backend.
    Messages arrive via send_query (from the agent loop injecting channel messages).
    Responses come from inject_user_input (called by server when human types).

    Routing: inject_user_input("[to:X] message") → backend parses and delivers
    directly to X's channel via channel_bus. No LLM needed for routing.
    """

    def __init__(self, on_event: Callable[[str, Any], Awaitable[None]] | None = None,
                 channel_bus: Any = None):
        self._config: BackendConfig | None = None
        self._input_queue: asyncio.Queue[str] = asyncio.Queue()
        self._connected = False
        self._session_id = "user_session"
        self._messages: list[BackendMessage] = []
        self._on_event = on_event  # callback for block/unblock events
        self._channel_bus = channel_bus  # for direct message delivery
        self._pending_block_from: str | None = None  # agent that triggered the block

    async def connect(self, config: BackendConfig) -> None:
        self._config = config
        self._connected = True
        logger.info("[USER] Backend connected")

    async def send_query(self, prompt: str) -> None:
        """Receive a message from the swarm (injected by agent loop on message arrival).

        Emits the message immediately to UI (via on_event) so user sees it without
        waiting for receive_messages to complete. Also detects [BLOCKED_ON_USER].
        """
        # Ignore internal wake-up signals
        if "__user_input_ready__" in prompt:
            return

        self._messages.append(BackendMessage(type="text", content=prompt))

        # Emit to UI immediately so user sees incoming messages
        if self._on_event:
            await self._on_event("user_message_received", {"message": prompt})

        # Detect blocking request
        if BLOCKED_PREFIX in prompt:
            # Extract sender from the "[From X]:" pattern
            sender = "unknown"
            if "[From " in prompt:
                try:
                    sender = prompt.split("[From ")[1].split("]")[0]
                except (IndexError, ValueError):
                    pass
            self._pending_block_from = sender
            logger.info(f"[USER] BLOCKED_ON_USER triggered by '{sender}'")
            if self._on_event:
                await self._on_event("blocked_on_user", {"from": sender, "message": prompt})

    async def receive_messages(self) -> AsyncIterator[BackendMessage]:
        """Wait for user input from the UI/Slack, then deliver it.

        Parses [to:X] prefix and routes directly to X's channel.
        This blocks until the human provides input via inject_user_input().
        """
        response = await self._input_queue.get()

        # Unblock if we were blocked
        if self._pending_block_from:
            logger.info(f"[USER] Unblocked by user response (was blocked by '{self._pending_block_from}')")
            if self._on_event:
                await self._on_event("unblocked_by_user", {"was_blocked_by": self._pending_block_from})
            self._pending_block_from = None

        # Parse [to:X] and deliver directly to target's channel
        if response.startswith("[to:") and "]" in response:
            target = response[4:response.index("]")]
            message = response[response.index("]") + 1:].strip()
            if self._channel_bus:
                target_channel = f"{target}:messages"
                await self._channel_bus.send_to(target_channel, sender="user", payload=message)
                logger.info(f"[USER] Delivered to '{target}': {message[:80]}...")
                yield BackendMessage(type="text", content=f"Message delivered to {target}.")
            else:
                yield BackendMessage(type="text", content=f"ERROR: No channel bus available.")
        else:
            yield BackendMessage(type="text", content=response)

        yield BackendMessage(
            type="result",
            raw_result=response,
            cost_usd=0.0,
            num_turns=0,
            session_id=self._session_id,
        )

    async def interrupt(self) -> None:
        pass

    async def disconnect(self) -> None:
        self._connected = False

    async def reconnect(self) -> bool:
        self._connected = True
        return True

    async def get_context_percentage(self) -> float | None:
        return None

    @property
    def model_name(self) -> str | None:
        return "human"

    @property
    def messages(self) -> list[BackendMessage]:
        return self._messages

    def inject_user_input(self, text: str) -> None:
        """Called by the server/Slack/etc when the user types a response.
        Also sends a wake-up signal on the user's message channel so the agent
        loop exits _wait_for_wakeup and calls receive_messages again."""
        self._input_queue.put_nowait(text)
        # Wake the agent loop by sending a signal on the channel
        if self._channel_bus:
            import asyncio
            channel = self._channel_bus.get_or_create("user:messages")
            asyncio.ensure_future(
                self._channel_bus.send_to("user:messages", sender="ui", payload="__user_input_ready__")
            )
