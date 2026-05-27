"""NudgeMonitor: background timer-based rule evaluation system.

Runs as a background asyncio task. Maintains a centralized pending_replies tracker
for all agents. Evaluates rules on a timer (every 30s) and sends nudge messages
directly to agents via the channel bus.

Rules are loaded from a swarm-specific Python module at runtime.
"""

from __future__ import annotations

import asyncio
import importlib
import logging
import random
import time
from typing import Any, Callable

from ._channels import ChannelBus
from ._telemetry import TelemetryStream, TelemetryView

logger = logging.getLogger("strataswarm.nudge")


class PendingRepliesTracker:
    """Tracks pending replies per agent — who has been asked but not yet responded."""

    def __init__(self):
        # agent_name -> list of (sender, timestamp) awaiting reply
        self._pending: dict[str, list[tuple[str, float]]] = {}

    def add_pending(self, agent_name: str, sender: str) -> None:
        """Record that agent_name received a message from sender and owes a reply."""
        if agent_name not in self._pending:
            self._pending[agent_name] = []
        self._pending[agent_name].append((sender, time.time()))

    def resolve_pending(self, agent_name: str, recipient: str) -> bool:
        """Agent sent a message to recipient — remove from pending if it was owed.
        Returns True if this resolved a pending reply."""
        if agent_name not in self._pending:
            return False
        for i, (sender, _ts) in enumerate(self._pending[agent_name]):
            if sender == recipient:
                self._pending[agent_name].pop(i)
                return True
        return False

    def get_pending(self, agent_name: str) -> list[tuple[str, float]]:
        """Get list of (sender, timestamp) that agent_name hasn't replied to."""
        return self._pending.get(agent_name, [])

    def get_overdue(self, agent_name: str, timeout_seconds: float = 300) -> list[str]:
        """Get senders that have been waiting longer than timeout_seconds."""
        now = time.time()
        return [
            sender for sender, ts in self.get_pending(agent_name)
            if now - ts > timeout_seconds
        ]

    def get_next_expected(self, agent_name: str) -> str | None:
        """Get the next sender the agent should reply to (FIFO)."""
        pending = self.get_pending(agent_name)
        return pending[0][0] if pending else None


class NudgeMonitor:
    """Background rule evaluation agent that sends tips to swarm agents.

    Runs as an asyncio task. Every `check_interval` seconds:
    1. For each agent, evaluate time-based rules against telemetry + pending state
    2. If a rule fires (probability gate passes, cooldown allows), send a message
       to the agent via the channel bus as "TipAgent"
    """

    def __init__(
        self,
        module_name: str | None,
        telemetry: TelemetryStream,
        channel_bus: ChannelBus | None = None,
        check_interval: float = 30.0,
    ):
        self._telemetry = telemetry
        self._channel_bus = channel_bus
        self._check_interval = check_interval
        self._rules: list[tuple[Callable[[TelemetryView], str | None], float, float]] = []
        self._cooldowns: dict[tuple[str, int], float] = {}  # (agent, rule_idx) -> next_fire_time
        self._super_agents: set[str] = set()
        self._agents: set[str] = set()
        self.pending = PendingRepliesTracker()
        self._task: asyncio.Task | None = None
        self._history: list[dict[str, Any]] = []  # nudge evaluation history
        self._max_history: int = 500

        if module_name:
            for candidate in [module_name, f"swarm_nudges.{module_name}"]:
                try:
                    mod = importlib.import_module(candidate)
                    self._rules = mod.RULES
                    logger.info(f"Loaded {len(self._rules)} nudge rules from {candidate}")
                    break
                except ImportError:
                    continue
            else:
                logger.warning(f"Could not load nudge module '{module_name}'")

    @property
    def rules_loaded(self) -> int:
        return len(self._rules)

    def start(self) -> None:
        """Start the background nudge loop."""
        if self._task is None or self._task.done():
            self._task = asyncio.create_task(self._run_loop())
            logger.info(f"[NUDGE] Background monitor started (interval={self._check_interval}s)")

    def stop(self) -> None:
        """Stop the background nudge loop."""
        if self._task and not self._task.done():
            self._task.cancel()

    async def _run_loop(self) -> None:
        """Background loop: evaluate rules for all agents periodically."""
        while True:
            await asyncio.sleep(self._check_interval)
            try:
                await self._evaluate_all()
            except Exception as e:
                logger.error(f"[NUDGE] Loop error: {e}")

    async def _evaluate_all(self) -> None:
        """Evaluate rules for all tracked agents and send tips."""
        if not self._rules or not self._channel_bus:
            return

        now = time.time()
        for agent_name in list(self._agents):
            tip = self._evaluate_agent(agent_name, now)
            if tip:
                await self._send_tip(agent_name, tip)

    def _evaluate_agent(self, agent_name: str, now: float) -> str | None:
        """Evaluate all rules for one agent. Returns tip or None."""
        view = TelemetryView(
            agent=agent_name,
            stream=self._telemetry,
            is_super=agent_name in self._super_agents,
            pending_tracker=self.pending,
        )

        for i, (rule_fn, prob, cooldown_seconds) in enumerate(self._rules):
            key = (agent_name, i)
            rule_name = rule_fn.__name__

            # Time-based cooldown
            if now < self._cooldowns.get(key, 0):
                self._log_history(now, agent_name, rule_name, i, "cooldown",
                                  f"on cooldown until {self._cooldowns[key]:.0f}")
                continue

            # Evaluate rule
            try:
                tip = rule_fn(view)
            except Exception as e:
                logger.error(f"Nudge rule {i} error for '{agent_name}': {e}")
                self._log_history(now, agent_name, rule_name, i, "error", str(e))
                continue

            if tip is None:
                continue  # rule didn't match — not logged (too noisy)

            # Probability gate
            roll = random.random()
            if roll > prob:
                self._log_history(now, agent_name, rule_name, i, "probability_skip",
                                  f"roll={roll:.2f} > prob={prob}")
                continue

            # Fire — set cooldown and return
            self._cooldowns[key] = now + cooldown_seconds
            self._log_history(now, agent_name, rule_name, i, "fired", tip)
            logger.info(f"[NUDGE] Fired for {agent_name} (rule {i}): {tip}")
            return tip

        return None

    def _log_history(self, ts: float, agent: str, rule: str, rule_idx: int,
                     outcome: str, detail: str) -> None:
        """Record a nudge evaluation event."""
        self._history.append({
            "timestamp": ts,
            "agent": agent,
            "rule": rule,
            "rule_idx": rule_idx,
            "outcome": outcome,  # "fired" | "cooldown" | "probability_skip" | "error"
            "detail": detail,
        })
        if len(self._history) > self._max_history:
            self._history = self._history[-self._max_history:]

    def get_history(self, limit: int = 100) -> list[dict[str, Any]]:
        """Get recent nudge evaluation history."""
        return self._history[-limit:]

    async def _send_tip(self, agent_name: str, tip: str) -> None:
        """Send a tip to an agent as a message from TipAgent (noreply)."""
        payload = f"{tip} [noreply@TipAgent — do NOT send_message to TipAgent]"
        channel_name = f"{agent_name}:messages"
        await self._channel_bus.send_to(channel_name, sender="TipAgent", payload=payload)
        logger.info(f"[NUDGE] Sent to {agent_name}: {tip}")

    # Legacy method for backward compat (called from agent between turns)
    def after_agent_turn(self, agent_name: str) -> str | None:
        """Legacy: evaluate rules synchronously. Returns tip or None.
        Prefer the background loop instead."""
        if not self._rules:
            return None
        now = time.time()
        return self._evaluate_agent(agent_name, now)
