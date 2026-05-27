"""Telemetry system: event recording and time-based querying.

Records events per agent. TelemetryView provides time-based queries
for nudge rules (e.g., "has this agent sent a message in the last 5 minutes?").
"""

import time
from typing import Any
from dataclasses import dataclass, field
from collections import deque


@dataclass
class TelemetryEvent:
    agent: str
    timestamp: float
    event_type: str          # "tool_call" | "message_sent" | "message_received" | "spawn"
    tool_name: str | None = None
    tool_args: dict | None = None
    target: str | None = None    # for messages: recipient name
    source: str | None = None    # for messages: sender name
    success: bool = True
    duration_ms: int | None = None


class TelemetryStream:
    def __init__(self, max_events_per_agent: int = 500):
        self._events: dict[str, deque[TelemetryEvent]] = {}
        self._max = max_events_per_agent

    def record(self, event: TelemetryEvent):
        agent = event.agent
        if agent not in self._events:
            self._events[agent] = deque(maxlen=self._max)
        self._events[agent].append(event)

    def get_recent(self, agent: str, n: int = 50) -> list[TelemetryEvent]:
        events = self._events.get(agent, deque())
        return list(events)[-n:]

    def get_all(self) -> dict[str, list[TelemetryEvent]]:
        return {k: list(v) for k, v in self._events.items()}

    def get_events_since(self, agent: str, since: float) -> list[TelemetryEvent]:
        """Get all events for agent since a given timestamp."""
        events = self._events.get(agent, deque())
        return [e for e in events if e.timestamp >= since]


class TelemetryView:
    """Time-based query interface for nudge rules.

    All queries are time-based: "did X happen in the last N seconds?"
    No more confusing 'within_turns' — just seconds.
    """

    def __init__(self, agent: str, stream: TelemetryStream, is_super: bool = False,
                 is_reply_only: bool = False, pending_tracker: Any = None):
        self._agent = agent
        self._stream = stream
        self._is_super = is_super
        self._is_reply_only = is_reply_only
        self._pending_tracker = pending_tracker

    def agent_is_super(self) -> bool:
        return self._is_super

    # --- Pending replies (from NudgeMonitor's PendingRepliesTracker) ---

    def pending_replies(self) -> list[tuple[str, float]]:
        """Get list of (sender, timestamp) this agent hasn't replied to."""
        if self._pending_tracker:
            return self._pending_tracker.get_pending(self._agent)
        return []

    def overdue_replies(self, timeout_seconds: float = 300) -> list[str]:
        """Get senders waiting longer than timeout_seconds for a reply."""
        if self._pending_tracker:
            return self._pending_tracker.get_overdue(self._agent, timeout_seconds)
        return []

    # --- Event queries (all time-based) ---

    @property
    def _events(self) -> list[TelemetryEvent]:
        return self._stream.get_recent(self._agent, n=200)

    def last_event_time(self) -> float | None:
        """Timestamp of most recent event, or None if no events."""
        events = self._events
        return events[-1].timestamp if events else None

    def seconds_since_last_event(self) -> float:
        """Seconds elapsed since last event. Returns inf if no events."""
        t = self.last_event_time()
        return time.time() - t if t else float("inf")

    def event_count(self, event_type: str | None = None, since_seconds: float = 300) -> int:
        """Count events of a given type in the last N seconds."""
        cutoff = time.time() - since_seconds
        events = [e for e in self._events if e.timestamp >= cutoff]
        if event_type:
            events = [e for e in events if e.event_type == event_type]
        return len(events)

    def tool_used(self, name: str, since_seconds: float = 120) -> bool:
        """Was tool `name` used in the last N seconds?"""
        cutoff = time.time() - since_seconds
        return any(
            e.event_type == "tool_call" and (name == "*" or e.tool_name == name)
            and e.timestamp >= cutoff
            for e in self._events
        )

    def tool_used_count(self, name: str, since_seconds: float = 300) -> int:
        """How many times was tool `name` used in the last N seconds?"""
        cutoff = time.time() - since_seconds
        return sum(
            1 for e in self._events
            if e.event_type == "tool_call" and (name == "*" or e.tool_name == name)
            and e.timestamp >= cutoff
        )

    def message_sent_to(self, agent: str, since_seconds: float = 120) -> bool:
        """Was a message sent to `agent` in the last N seconds?"""
        cutoff = time.time() - since_seconds
        return any(
            e.event_type == "message_sent"
            and (agent == "*" or e.target == agent)
            and e.timestamp >= cutoff
            for e in self._events
        )

    def last_message_sent_to(self, agent: str) -> TelemetryEvent | None:
        """Most recent message sent to `agent`, or None."""
        for e in reversed(self._events):
            if e.event_type == "message_sent" and e.target == agent:
                return e
        return None

    def message_received_from(self, pattern: str, since_seconds: float = 300) -> list[TelemetryEvent]:
        """Messages received from agents matching pattern in last N seconds."""
        import fnmatch
        cutoff = time.time() - since_seconds
        return [
            e for e in self._events
            if e.event_type == "message_received"
            and e.source and fnmatch.fnmatch(e.source, pattern)
            and e.timestamp >= cutoff
        ]

    def messages_containing(self, text: str, since_seconds: float = 300) -> list[TelemetryEvent]:
        """Messages containing text in last N seconds."""
        cutoff = time.time() - since_seconds
        return [
            e for e in self._events
            if e.timestamp >= cutoff
            and e.tool_args and text in str(e.tool_args.get("raw", ""))
        ]

    def elapsed_since(self, event: TelemetryEvent) -> float:
        """Seconds since a specific event."""
        return time.time() - event.timestamp

    def is_idle(self, idle_seconds: float = 60) -> bool:
        """Has the agent had no events for idle_seconds?"""
        return self.seconds_since_last_event() > idle_seconds
