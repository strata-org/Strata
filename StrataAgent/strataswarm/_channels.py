from __future__ import annotations

import asyncio
import json
import logging
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

logger = logging.getLogger(__name__)


@dataclass
class ChannelMessage:
    sender: str
    payload: Any
    topic: str = ""


@dataclass
class MailEntry:
    """One message in the persistent mailbox. Immutable once created.

    Subject is stored BARE (no "RE:" prefix); "RE:" is prepended at render time
    only. Read-state is NOT stored here — it lives in Mailbox._unread (in-memory
    only, not journaled). See strataswarm/modules/messaging_overhaul.md §2-2.1.
    """
    msg_id: int
    thread_id: int
    sender: str
    recipient: str
    subject: str
    body: str
    timestamp: datetime
    in_reply_to: int | None = None

    def to_record(self) -> dict[str, Any]:
        return {
            "msg_id": self.msg_id,
            "thread_id": self.thread_id,
            "in_reply_to": self.in_reply_to,
            "subject": self.subject,
            "sender": self.sender,
            "recipient": self.recipient,
            "ts": self.timestamp.isoformat(),
            "body": self.body,
        }

    @classmethod
    def from_record(cls, rec: dict[str, Any]) -> "MailEntry":
        return cls(
            msg_id=int(rec["msg_id"]),
            thread_id=int(rec["thread_id"]),
            sender=str(rec["sender"]),
            recipient=str(rec["recipient"]),
            subject=str(rec.get("subject", "")),
            body=str(rec.get("body", "")),
            timestamp=datetime.fromisoformat(rec["ts"]),
            in_reply_to=(int(rec["in_reply_to"]) if rec.get("in_reply_to") is not None else None),
        )


def _synthesize_subject(body: str, max_words: int = 6) -> str:
    """A short handle for a thread when the sender didn't supply a subject."""
    words = body.strip().split()
    if not words:
        return "(no subject)"
    head = " ".join(words[:max_words])
    return head + ("…" if len(words) > max_words else "")


class Mailbox:
    """Persistent, append-only, per-agent mailbox.

    Messages are never deleted. "Read" is a per-agent marker (in-memory only) over
    the permanent log — browsing headers never changes it; reading a body does.

    On-disk: a single append-only JSONL MESSAGE log (one record per message; no
    read-events). Read-state is deliberately NOT journaled — on reload we assume
    everything is read (empty unread). Losing transient read-state across a restart
    is acceptable; the message history is what's durable.
    See strataswarm/modules/messaging_overhaul.md §2.1.
    """

    def __init__(self) -> None:
        self._entries: dict[int, MailEntry] = {}          # msg_id -> entry
        self._order: list[int] = []                       # global append order
        self._inbox: dict[str, list[int]] = {}            # recipient -> [msg_id]
        self._unread: dict[str, set[int]] = {}            # recipient -> {msg_id}
        self._threads: dict[int, list[int]] = {}          # thread_id -> [msg_id]
        self._next_msg_id: int = 1
        self._path: Path | None = None
        self._fh: Any | None = None

    # ── durable journal ────────────────────────────────────────────────────
    def bind_file(self, path: Path) -> None:
        """Point the mailbox at its JSONL journal, replaying any existing content.

        Idempotent-safe to call once after the session dir exists. Replay marks
        everything read (unread starts empty)."""
        self._path = path
        if path.exists():
            self._replay(path)
        # Open for append AFTER replay so we don't re-read our own writes.
        self._fh = open(path, "a", buffering=1)  # line-buffered, matches SessionLogger

    def _replay(self, path: Path) -> None:
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except Exception as e:  # unreadable file — start fresh rather than crash
            logger.warning("Mailbox: could not read %s (%s); starting empty", path, e)
            return
        for i, line in enumerate(lines):
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
                entry = MailEntry.from_record(rec)
            except Exception as e:
                # Torn/partial trailing line from a crash mid-append: skip it.
                # Only the last line should ever be malformed; log and move on.
                logger.warning("Mailbox: skipping malformed record at line %d in %s (%s)", i + 1, path, e)
                continue
            self._index(entry)  # rebuild state; does NOT append to file
        # Reload rule: assume everything read.
        self._unread = {}
        self._next_msg_id = (max(self._entries) + 1) if self._entries else 1

    def _index(self, entry: MailEntry) -> None:
        """File an entry into the in-memory indices (used by both replay and deliver)."""
        self._entries[entry.msg_id] = entry
        self._order.append(entry.msg_id)
        self._inbox.setdefault(entry.recipient, []).append(entry.msg_id)
        self._unread.setdefault(entry.recipient, set()).add(entry.msg_id)
        self._threads.setdefault(entry.thread_id, []).append(entry.msg_id)

    def _append_record(self, entry: MailEntry) -> None:
        if self._fh is None:
            return
        try:
            self._fh.write(json.dumps(entry.to_record(), ensure_ascii=False) + "\n")
        except Exception as e:
            logger.warning("Mailbox: failed to journal msg %d (%s)", entry.msg_id, e)

    # ── send ────────────────────────────────────────────────────────────────
    def _resolve_thread(
        self, sender: str, recipient: str, in_reply_to: int | None
    ) -> tuple[int | None, int | None]:
        """Return (in_reply_to, thread_id-or-None). thread_id None => start fresh.

        Explicit in_reply_to wins. Otherwise infer from the most recent message the
        recipient sent back to this sender (the open exchange between the two)."""
        if in_reply_to is not None and in_reply_to in self._entries:
            return in_reply_to, self._entries[in_reply_to].thread_id
        # Infer: last message where the recipient wrote to this sender.
        for msg_id in reversed(self._order):
            e = self._entries[msg_id]
            if e.sender == recipient and e.recipient == sender:
                return e.msg_id, e.thread_id
        return None, None

    def deliver(
        self,
        sender: str,
        recipient: str,
        body: str,
        subject: str | None = None,
        in_reply_to: int | None = None,
    ) -> MailEntry:
        """Append a message to the recipient's mailbox and return the created entry."""
        msg_id = self._next_msg_id
        self._next_msg_id += 1

        # An explicit subject with no in_reply_to names a NEW thread — the sender is
        # opening a topic, not continuing one. Only infer a thread when the sender
        # gave neither in_reply_to nor a subject ("continue what we were saying").
        if in_reply_to is None and subject and subject.strip():
            resolved_reply, thread_id = None, None
        else:
            resolved_reply, thread_id = self._resolve_thread(sender, recipient, in_reply_to)
        if thread_id is None:
            thread_id = msg_id  # fresh thread rooted at this message
            subj = subject.strip() if subject and subject.strip() else _synthesize_subject(body)
        else:
            # Reply: inherit the thread root's subject (stored bare).
            root = self._entries.get(thread_id)
            subj = root.subject if root else (subject or _synthesize_subject(body))

        entry = MailEntry(
            msg_id=msg_id,
            thread_id=thread_id,
            sender=sender,
            recipient=recipient,
            subject=subj,
            body=body,
            timestamp=datetime.now(),
            in_reply_to=resolved_reply,
        )
        self._index(entry)
        self._append_record(entry)
        return entry

    # ── read-state ────────────────────────────────────────────────────────
    def unread_ids(self, agent: str) -> list[int]:
        """msg_ids unread by `agent`, oldest first."""
        s = self._unread.get(agent)
        if not s:
            return []
        return sorted(s)

    def unread_count(self, agent: str) -> int:
        return len(self._unread.get(agent, ()))

    def mark_read(self, agent: str, msg_ids: int | list[int]) -> None:
        s = self._unread.get(agent)
        if not s:
            return
        if isinstance(msg_ids, int):
            s.discard(msg_ids)
        else:
            for mid in msg_ids:
                s.discard(mid)

    # ── queries (do NOT mark read; callers decide) ──────────────────────────
    def get(self, msg_id: int) -> MailEntry | None:
        return self._entries.get(msg_id)

    def inbox(self, agent: str) -> list[MailEntry]:
        """All messages received by `agent`, oldest first."""
        return [self._entries[m] for m in self._inbox.get(agent, [])]

    def recent(self, agent: str, limit: int = 10) -> list[MailEntry]:
        """The most recent `limit` messages received by `agent`, oldest→newest."""
        ids = self._inbox.get(agent, [])
        return [self._entries[m] for m in ids[-limit:]]

    def oldest_unread(self, agent: str) -> MailEntry | None:
        ids = self.unread_ids(agent)
        return self._entries[ids[0]] if ids else None

    def unread_entries(self, agent: str) -> list[MailEntry]:
        return [self._entries[m] for m in self.unread_ids(agent)]

    def from_sender(self, agent: str, sender: str, last: int = 1) -> list[MailEntry]:
        """Last `last` messages `agent` received from `sender`, oldest→newest."""
        matches = [self._entries[m] for m in self._inbox.get(agent, [])
                   if self._entries[m].sender == sender]
        return matches[-last:] if last > 0 else matches

    def thread_ids(self, id_: int) -> list[int]:
        """Resolve a thread_id OR any msg_id in a thread to the full ordered id list."""
        if id_ in self._threads:
            tid = id_
        elif id_ in self._entries:
            tid = self._entries[id_].thread_id
        else:
            return []
        return list(self._threads.get(tid, []))

    def thread_slice(
        self, id_: int, start: int = 0, end: int | None = None
    ) -> tuple[list[MailEntry], int]:
        """Return (entries[start:end], total_in_thread). Shows both sides in order."""
        ids = self.thread_ids(id_)
        total = len(ids)
        sliced = ids[start:end] if end is not None else ids[start:]
        return [self._entries[m] for m in sliced], total

    def close(self) -> None:
        if self._fh is not None:
            try:
                self._fh.close()
            except Exception:
                pass
            self._fh = None


class Channel:
    def __init__(self, name: str, maxsize: int = 0) -> None:
        self.name = name
        self._queue: asyncio.Queue[ChannelMessage] = asyncio.Queue(maxsize)
        self._subscribers: list[asyncio.Queue[ChannelMessage]] = []
        self._locked: bool = False
        self._queue_during_lock: list[ChannelMessage] = []

    def lock(self) -> None:
        self._locked = True

    def unlock(self) -> None:
        self._locked = False
        for msg in self._queue_during_lock:
            self._queue.put_nowait(msg)
            for sub in self._subscribers:
                sub.put_nowait(msg)
        self._queue_during_lock.clear()

    async def send(self, msg: ChannelMessage) -> None:
        if self._locked:
            self._queue_during_lock.append(msg)
            return
        await self._queue.put(msg)
        for sub in self._subscribers:
            await sub.put(msg)

    async def receive(self, timeout: float | None = None) -> ChannelMessage | None:
        try:
            if timeout is not None and timeout <= 0:
                return self._queue.get_nowait()
            return await asyncio.wait_for(self._queue.get(), timeout=timeout)
        except (asyncio.TimeoutError, asyncio.QueueEmpty):
            return None

    @property
    def pending_count(self) -> int:
        return self._queue.qsize()

    def peek_summary(self) -> list[tuple[str, str]]:
        """Non-destructive peek: returns (sender, topic) for each pending message."""
        return [(msg.sender, msg.topic) for msg in list(self._queue._queue)]

    async def wait_for_message(self, timeout: float | None = None) -> bool:
        """Block until at least one message is in the queue. Does NOT consume it.
        Returns True if a message is available, False on timeout."""
        if self._queue.qsize() > 0:
            return True
        # Subscribe temporarily to get notified on next send
        notify: asyncio.Queue[ChannelMessage] = asyncio.Queue(maxsize=1)
        self._subscribers.append(notify)
        try:
            await asyncio.wait_for(notify.get(), timeout=timeout)
            return True
        except (asyncio.TimeoutError, asyncio.CancelledError):
            return False
        finally:
            self._subscribers.remove(notify)

    def subscribe(self) -> asyncio.Queue[ChannelMessage]:
        q: asyncio.Queue[ChannelMessage] = asyncio.Queue()
        self._subscribers.append(q)
        return q

    def unsubscribe(self, q: asyncio.Queue[ChannelMessage]) -> None:
        self._subscribers.remove(q)


class ChannelBus:
    def __init__(self) -> None:
        self._channels: dict[str, Channel] = {}
        # Persistent, append-only mailbox shared by all agents on this bus. Starts
        # in-memory only; bind_mailbox_file() attaches the JSONL journal once the
        # session dir exists (the bus is constructed before it — _swarm.py).
        self.mailbox = Mailbox()

    def bind_mailbox_file(self, path: Path) -> None:
        """Attach the mailbox's durable JSONL journal, replaying existing content."""
        self.mailbox.bind_file(path)

    def get_or_create(self, name: str, maxsize: int = 0) -> Channel:
        if name not in self._channels:
            self._channels[name] = Channel(name, maxsize)
        return self._channels[name]

    def __getitem__(self, name: str) -> Channel:
        return self.get_or_create(name)

    async def send_to(self, channel_name: str, sender: str, payload: Any, topic: str = "") -> None:
        ch = self.get_or_create(channel_name)
        await ch.send(ChannelMessage(sender=sender, payload=payload, topic=topic))
