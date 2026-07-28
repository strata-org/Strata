"""Process-global authentication circuit breaker (Bug #4).

Motivation
----------
Long unattended runs die a slow, expensive death when the Claude/Bedrock
credentials expire mid-flight: every agent's backend call fails with an auth
error, each failure is caught by the generic exception funnel, the agent
"recovers" by reconnecting (which also fails), and the swarm spins — burning
wall-clock and, worse, retry cost — with no human around to refresh creds. The
prover watchdog can't see this (it only sees "no completion"), so it just keeps
restarting a prover that can never authenticate.

Design — "pause + poll to resume" (the option chosen for this bug)
------------------------------------------------------------------
A single process-global breaker gates EVERY agent's API calls through one
shared asyncio.Event, so we don't have to reach into every per-agent PauseToken:

    CLOSED   (healthy)  gate set   → agents proceed
    OPEN     (tripped)  gate clear → agents block in wait_if_tripped()
    HALF_OPEN (probing) gate set   → agents proceed AS PROBES

Transitions:
  * record_failure() on an auth-classified error: bump the consecutive counter.
    From CLOSED, once it reaches FAIL_THRESHOLD → trip to OPEN (clear the gate,
    launch the poller). From HALF_OPEN, a fresh failure means the probe failed →
    back to OPEN with a longer backoff.
  * record_success() (any clean backend message): reset the counter; if we were
    OPEN/HALF_OPEN, the creds are valid again → CLOSED (set the gate).
  * poller task: sleeps an exponential backoff, then flips OPEN→HALF_OPEN and
    re-opens the gate so the next real API calls act as probes. If they succeed
    the breaker closes; if they fail it re-trips with a longer backoff. This is
    the "poll to resume" — no assumption about the creds mechanism (API key vs.
    Bedrock vs. subscription), we just let real traffic prove liveness.

Non-auth errors never trip the breaker — they flow through the existing
per-agent recovery paths untouched.
"""

from __future__ import annotations

import asyncio
import logging

logger = logging.getLogger(__name__)

# Number of consecutive auth failures (across ALL agents) before tripping.
FAIL_THRESHOLD = 3
# Backoff schedule for the poller's half-open probes (seconds). The last value
# repeats for every subsequent failed probe.
BACKOFF_SCHEDULE = (30, 60, 120, 300, 600)

# Substrings that identify an authentication / credential-expiry failure.
# Matched case-insensitively against the stringified exception.
_AUTH_MARKERS = (
    "security token",
    "expiredtoken",
    "expired token",
    "the security token included in the request is expired",
    "unable to locate credentials",
    "credential",
    "unauthorized",
    "invalid api key",
    "invalid x-api-key",
    "authentication",
    "authenticationerror",
    "403",
    "401",
    "access denied",
    "accessdenied",
    "not authorized",
    "forbidden",
)


def is_auth_error(exc: BaseException | str) -> bool:
    """Best-effort classification of an exception (or message) as an auth failure.

    Conservative on the false-positive side: we only trip on markers that are
    overwhelmingly credential/permission related. A plain ConnectionError or a
    Lean/tool error will NOT match.
    """
    text = str(exc).lower()
    if not text:
        return False
    return any(marker in text for marker in _AUTH_MARKERS)


class AuthCircuitBreaker:
    """Process-global breaker. Use the module-level singleton via get_breaker()."""

    def __init__(self) -> None:
        self._gate = asyncio.Event()
        self._gate.set()  # start healthy/closed
        self._lock = asyncio.Lock()
        self._consecutive = 0
        self._backoff_idx = 0
        self._state = "closed"  # closed | open | half_open
        self._poller: asyncio.Task | None = None
        # Optional hook invoked (state, detail) on every transition — the swarm
        # wires this to surface breaker events on the dashboard.
        self.on_event = None

    @property
    def is_tripped(self) -> bool:
        return self._state == "open"

    @property
    def state(self) -> str:
        return self._state

    async def wait_if_tripped(self) -> None:
        """Block while the breaker is OPEN. Cheap no-op when healthy."""
        if self._gate.is_set():
            return
        logger.warning("[AUTH-BREAKER] request blocked — waiting for credentials to recover")
        await self._gate.wait()

    async def record_success(self) -> None:
        """A clean backend response — creds are valid. Reset and close if needed."""
        if self._state == "closed" and self._consecutive == 0:
            return  # hot path: nothing to do
        async with self._lock:
            self._consecutive = 0
            self._backoff_idx = 0
            if self._state != "closed":
                self._state = "closed"
                self._gate.set()
                self._cancel_poller()
                logger.info("[AUTH-BREAKER] credentials recovered — CLOSED")
                await self._notify("closed", "credentials recovered")

    async def record_failure(self, exc: BaseException | str) -> bool:
        """Record a failure. Returns True if it was classified as auth-related.

        Trips the breaker (or re-opens from half-open) on auth failures once the
        consecutive count crosses the threshold. Non-auth failures are ignored.
        """
        if not is_auth_error(exc):
            return False
        async with self._lock:
            self._consecutive += 1
            detail = str(exc)[:200]
            if self._state == "half_open":
                # A probe failed: creds still bad. Re-open with a longer backoff.
                self._state = "open"
                self._gate.clear()
                self._backoff_idx = min(self._backoff_idx + 1, len(BACKOFF_SCHEDULE) - 1)
                logger.warning(f"[AUTH-BREAKER] probe failed — re-OPEN (backoff idx {self._backoff_idx})")
                await self._notify("open", detail)
                self._schedule_poller()
            elif self._state == "closed" and self._consecutive >= FAIL_THRESHOLD:
                self._state = "open"
                self._gate.clear()
                self._backoff_idx = 0
                logger.error(
                    f"[AUTH-BREAKER] TRIPPED after {self._consecutive} consecutive "
                    f"auth failures — pausing all agents. Last: {detail}")
                await self._notify("open", detail)
                self._schedule_poller()
        return True

    def _schedule_poller(self) -> None:
        self._cancel_poller()
        try:
            self._poller = asyncio.ensure_future(self._poll())
        except RuntimeError:
            # No running loop (shouldn't happen in the agent runtime) — leave the
            # gate open-tripped; a later record_success can still close it.
            self._poller = None

    def _cancel_poller(self) -> None:
        if self._poller is not None and not self._poller.done():
            self._poller.cancel()
        self._poller = None

    async def _poll(self) -> None:
        """After a backoff, half-open the gate so real traffic can probe creds."""
        delay = BACKOFF_SCHEDULE[min(self._backoff_idx, len(BACKOFF_SCHEDULE) - 1)]
        try:
            await asyncio.sleep(delay)
        except asyncio.CancelledError:
            return
        async with self._lock:
            if self._state != "open":
                return
            self._state = "half_open"
            self._gate.set()  # let the next calls through as probes
            logger.info(f"[AUTH-BREAKER] HALF-OPEN after {delay}s — probing credentials")
            await self._notify("half_open", f"probing after {delay}s")

    async def _notify(self, state: str, detail: str) -> None:
        if self.on_event is None:
            return
        try:
            res = self.on_event(state, detail)
            if asyncio.iscoroutine(res):
                await res
        except Exception:
            pass


_breaker: AuthCircuitBreaker | None = None


def get_breaker() -> AuthCircuitBreaker:
    """Get (or lazily create) the process-global auth circuit breaker."""
    global _breaker
    if _breaker is None:
        _breaker = AuthCircuitBreaker()
    return _breaker
