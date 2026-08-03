"""
In-process MCP tools for inter-agent messaging via ChannelBus.

Agents get `send_message`, mailbox pull tools (`list_recent_messages`,
`list_all_unread_mail`, `see_last_unread_mail`, `get_messages_by_sender`,
`get_thread`), `wait_for_reply`, and `get_time` tools automatically, letting them
communicate with other agents and track time.

Messages are delivered to a persistent, append-only per-agent mailbox
(`ChannelBus.mailbox`) — nothing is ever deleted, "read" is a per-agent marker.
See strataswarm/modules/messaging_overhaul.md.
"""

from __future__ import annotations

import asyncio
from collections.abc import Callable
from datetime import datetime
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from ._channels import ChannelBus, MailEntry


def render_mail(entry: MailEntry, mailbox: Any | None = None) -> str:
    """Full email-style render of one message. 'RE:' is prepended here (never stored).

    The '↳ Replying to #N "subject"' line lets a late/out-of-order reply still be
    understood — it names the message it answers.
    """
    ts = entry.timestamp.strftime("%Y-%m-%d %H:%M:%S")
    subject = ("RE: " + entry.subject) if entry.in_reply_to is not None else entry.subject
    lines = [
        f"[#{entry.msg_id}] From: {entry.sender}   {ts}",
        f"Subject: {subject}",
    ]
    if entry.in_reply_to is not None:
        parent_subj = ""
        if mailbox is not None:
            parent = mailbox.get(entry.in_reply_to)
            if parent is not None:
                parent_subj = f' "{parent.subject}"'
        lines.append(f"↳ Replying to #{entry.in_reply_to}{parent_subj}")
    lines.append("")
    lines.append(entry.body)
    return "\n".join(lines)


def render_header(entry: MailEntry, unread: bool = False) -> str:
    """One-line header for browse tools. Never marks read."""
    ts = entry.timestamp.strftime("%Y-%m-%d %H:%M:%S")
    subject = ("RE: " + entry.subject) if entry.in_reply_to is not None else entry.subject
    dot = "● " if unread else "  "
    return f"{dot}#{entry.msg_id} · {ts} · from {entry.sender} · {subject}"


def create_messaging_server(
    agent_name: str,
    channel_bus: ChannelBus,
    known_agents: list[str],
    can_message: Callable[[str, str], bool] | None = None,
    route_message: Callable[[str, str, str], str] | None = None,
    get_sender_display: Callable[[str], str] | None = None,
    on_tool_call: Callable[[str, str, dict], None] | None = None,
    reply_only_mode: bool = False,
    known_service_agents: set[str] | None = None,
    start_time: datetime | None = None,
    is_agent_alive: Callable[[str], bool] | None = None,
    outbound_limit: int | None = None,
    outbound_limit_response: str | None = None,
    get_inbound_limit: Callable[[str], tuple[int | None, str | None]] | None = None,
):
    """
    Create an MCP server exposing send_message, the mailbox pull tools, and
    wait_for_reply, bound to this agent's identity and the shared ChannelBus.
    """

    @tool(
        name="send_message",
        description=(
            "Send a message to another agent by name. It lands in their persistent "
            "mailbox (nothing is ever deleted) and they read it on their next turn. "
            "This is a NOTIFY — it returns a delivery status, never a reply; the "
            "recipient responds on its own turn if it chooses. Use 'subject' to name "
            "the topic. To reply within a thread, pass 'in_reply_to' with the message "
            "id (#N) you're answering (a 'RE:' prefix is added automatically). If you "
            "must wait for a specific reply before continuing, use wait_for_reply."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "to": {
                    "type": "string",
                    "description": "Name of the recipient agent.",
                },
                "message": {
                    "type": "string",
                    "description": "The message content to send.",
                },
                "subject": {
                    "type": "string",
                    "description": (
                        "Short topic for this message. Providing a subject with no "
                        "in_reply_to starts a NEW thread; omit it to continue the "
                        "current conversation with this agent."
                    ),
                },
                "in_reply_to": {
                    "type": "integer",
                    "description": (
                        "Message id (#N) you are replying to. Threads the message and "
                        "prefixes the subject with 'RE:' automatically."
                    ),
                },
            },
            "required": ["to", "message"],
        },
    )
    async def send_message(input: dict[str, Any]) -> dict[str, Any]:
        recipient = input["to"]
        message = input["message"]
        subject = input.get("subject")
        in_reply_to = input.get("in_reply_to")

        if recipient == agent_name:
            return {"content": [{"type": "text", "text": "ERROR: Cannot send a message to yourself."}]}

        if recipient == "TipAgent":
            return {"content": [{"type": "text", "text":
                "ERROR: TipAgent is a system agent (noreply@TipAgent). "
                "It cannot be responded to. Ignore its messages or act on the advice."}]}

        # reply_only enforcement: can only send to agents in pending_replies (FIFO)
        # EXCEPTION: messages to other reply_only (service) agents are "research queries"
        # and bypass the FIFO check. This lets reply_only agents consult each other.
        is_research_query = recipient in known_service_agents if known_service_agents else False
        if reply_only_mode and not is_research_query:
            if not pending_replies:
                return {"content": [{"type": "text", "text":
                    "ERROR: You are reply-only. No one has asked you anything yet. "
                    "Wait for a message first, then respond to the sender."}]}
            expected = pending_replies[0]
            if recipient != expected:
                return {"content": [{"type": "text", "text": (
                    f"ERROR: You are reply-only. You must reply to '{expected}' first (FIFO order). "
                    f"Pending replies to: {pending_replies}. "
                    f"Send your response to '{expected}', not '{recipient}'."
                )}]}

        # Enforce visibility graph: block messages to agents outside sender's visibility set
        if can_message is not None and not can_message(agent_name, recipient):
            return {"content": [{"type": "text", "text": (
                f"ERROR: Cannot message '{recipient}' — not in your visibility set. "
                f"Use list_agents() to see who you can communicate with."
            )}]}

        # Check if recipient is still alive (killed agents are gone)
        if is_agent_alive is not None and not is_agent_alive(recipient):
            # Pop from pending_replies if we owed them a reply
            if reply_only_mode and pending_replies and pending_replies[0] == recipient:
                pending_replies.pop(0)
            return {"content": [{"type": "text", "text": (
                f"Agent '{recipient}' is no longer running (killed or completed). "
                f"Message not delivered. Move on to the next task."
            )}]}

        # Enforce message length limits
        msg_len = len(message)
        # Sender's outbound limit
        if outbound_limit and msg_len > outbound_limit:
            resp = outbound_limit_response or "Shorten your message."
            return {"content": [{"type": "text", "text": (
                f"ERROR: Your message is {msg_len} chars but your outbound limit is "
                f"{outbound_limit} chars. {resp}"
            )}]}
        # Recipient's inbound limit
        if get_inbound_limit:
            inbound_limit, inbound_resp = get_inbound_limit(recipient)
            if inbound_limit and msg_len > inbound_limit:
                resp = inbound_resp or f"Keep messages to '{recipient}' under {inbound_limit} chars."
                return {"content": [{"type": "text", "text": (
                    f"ERROR: Message to '{recipient}' is {msg_len} chars but their inbound "
                    f"limit is {inbound_limit} chars. {resp}"
                )}]}

        # Rewrite sender name for sharded instances (transparent to recipient)
        sender_display = get_sender_display(agent_name) if get_sender_display else agent_name
        # Route to physical instance if sharded (transparent to sender)
        physical_recipient = route_message(recipient, message, agent_name) if route_message else recipient

        # Deliver to the persistent mailbox (append-only; nothing ever deleted).
        entry = channel_bus.mailbox.deliver(
            sender=sender_display,
            recipient=physical_recipient,
            body=message,
            subject=subject,
            in_reply_to=in_reply_to,
        )
        # Signal the recipient's wakeup channel so a sleeping agent wakes on new
        # mail. The payload carries the msg_id; content lives in the mailbox.
        messages_channel = f"{physical_recipient}:messages"
        await channel_bus.send_to(
            messages_channel, sender=sender_display, payload=entry.msg_id, topic=entry.subject
        )
        # Forced yield: hand the event loop to the recipient (or any peer waiting
        # on this wakeup) right now, before we return, so a concurrently-running
        # recipient gets a chance to observe the mail and start replying. This
        # enforces a context switch instead of relying on it happening later.
        await asyncio.sleep(0)

        # Only pop pending reply AFTER successful delivery
        if reply_only_mode and pending_replies and pending_replies[0] == recipient:
            pending_replies.pop(0)
        # Record telemetry
        if on_tool_call:
            on_tool_call(agent_name, "send_message", {"to": recipient})
        re_note = f" (RE: #{in_reply_to})" if in_reply_to else ""
        return {"content": [{"type": "text", "text": (
            f"Delivered to '{recipient}' as message #{entry.msg_id}{re_note}. "
            f"It will read this on its next turn and may reply then."
        )}]}

    mailbox = channel_bus.mailbox

    @tool(
        name="list_recent_messages",
        description=(
            "Browse the headers of your most recent messages (sender + subject + id), "
            "newest last. Does NOT mark anything read — use a read tool for the body."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "limit": {
                    "type": "integer",
                    "description": "How many recent headers to show. Default 10.",
                },
            },
            "required": [],
        },
    )
    async def list_recent_messages(input: dict[str, Any]) -> dict[str, Any]:
        limit = int(input.get("limit", 10))
        entries = mailbox.recent(agent_name, limit=limit)
        if not entries:
            return {"content": [{"type": "text", "text": "Your mailbox is empty."}]}
        unread = mailbox._unread.get(agent_name, set())
        header = f"Last {len(entries)} message(s) (● = unread):\n"
        body = "\n".join(render_header(e, unread=(e.msg_id in unread)) for e in entries)
        return {"content": [{"type": "text", "text": header + body}]}

    @tool(
        name="list_all_unread_mail",
        description=(
            "Browse the headers of every message you haven't read yet, oldest first. "
            "Does NOT mark anything read."
        ),
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def list_all_unread_mail(input: dict[str, Any]) -> dict[str, Any]:
        entries = mailbox.unread_entries(agent_name)
        if not entries:
            return {"content": [{"type": "text", "text": "You have no unread mail."}]}
        header = f"{len(entries)} unread message(s):\n"
        body = "\n".join(render_header(e, unread=True) for e in entries)
        return {"content": [{"type": "text", "text": header + body}]}

    @tool(
        name="see_last_unread_mail",
        description=(
            "Read your oldest unread message in full and mark it read. "
            "Call repeatedly to clear a backlog in arrival order."
        ),
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def see_last_unread_mail(input: dict[str, Any]) -> dict[str, Any]:
        entry = mailbox.oldest_unread(agent_name)
        if entry is None:
            return {"content": [{"type": "text", "text": "You have no unread mail."}]}
        mailbox.mark_read(agent_name, entry.msg_id)
        if on_tool_call and entry.sender != "TipAgent":
            on_tool_call(agent_name, "message_received", {"from": entry.sender})
        return {"content": [{"type": "text", "text": render_mail(entry, mailbox)}]}

    @tool(
        name="get_messages_by_sender",
        description=(
            "Read the last N messages you received from a specific sender (default 1), "
            "oldest to newest, in full. Marks them read."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "sender": {"type": "string", "description": "Name of the sender."},
                "last": {
                    "type": "integer",
                    "description": "How many of the most recent messages from this sender. Default 1.",
                },
            },
            "required": ["sender"],
        },
    )
    async def get_messages_by_sender(input: dict[str, Any]) -> dict[str, Any]:
        sender = input["sender"]
        last = int(input.get("last", 1))
        entries = mailbox.from_sender(agent_name, sender, last=last)
        if not entries:
            return {"content": [{"type": "text", "text": f"No messages from '{sender}'."}]}
        mailbox.mark_read(agent_name, [e.msg_id for e in entries])
        text = "\n\n".join(render_mail(e, mailbox) for e in entries)
        return {"content": [{"type": "text", "text": text}]}

    @tool(
        name="get_thread",
        description=(
            "Read a conversation thread in order, showing BOTH sides (your messages "
            "and the replies). Pass a thread id or any message id (#N) in the thread. "
            "Use start/end (0-based, end exclusive) to zoom into a slice — e.g. "
            "start=0, end=2 for a question and its reply. Marks the shown messages read."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "id": {"type": "integer", "description": "A thread id or any message id (#N) in the thread."},
                "start": {"type": "integer", "description": "Slice start index (0-based). Default 0."},
                "end": {"type": "integer", "description": "Slice end index (exclusive). Default: end of thread."},
            },
            "required": ["id"],
        },
    )
    async def get_thread(input: dict[str, Any]) -> dict[str, Any]:
        id_ = int(input["id"])
        start = int(input.get("start", 0))
        end = input.get("end")
        end = int(end) if end is not None else None
        # Cap an unbounded read so a long thread never floods the turn.
        MAX = 20
        bounded_end = end if end is not None else start + MAX
        entries, total = mailbox.thread_slice(id_, start, bounded_end)
        if not entries and total == 0:
            return {"content": [{"type": "text", "text": f"No thread found for #{id_}."}]}
        mailbox.mark_read(agent_name, [e.msg_id for e in entries])
        text = "\n\n".join(render_mail(e, mailbox) for e in entries)
        shown_end = (bounded_end if bounded_end is not None else total)
        remaining = total - min(shown_end, total)
        if remaining > 0:
            text += f"\n\n…{remaining} more message(s) in this thread — use start/end to see them."
        return {"content": [{"type": "text", "text": text}]}

    @tool(
        name="wait_for_reply",
        description=(
            "Block your turn until a message from a specific sender is available, then "
            "return it (marks read). If an unread message from that sender already "
            "exists, returns it immediately. On timeout, returns without a message. "
            "NOTE: this only pays off if the sender is an agent running right now "
            "(e.g. a peer during the same chunk); waiting on an idle agent just burns "
            "the timeout. Otherwise, fire your message and pick up the reply next turn."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "sender": {"type": "string", "description": "The agent whose reply you're waiting for."},
                "timeout": {
                    "type": "number",
                    "description": "Max seconds to wait. Default 60.",
                },
            },
            "required": ["sender"],
        },
    )
    async def wait_for_reply(input: dict[str, Any]) -> dict[str, Any]:
        sender = input["sender"]
        timeout = min(max(float(input.get("timeout", 60)), 0.1), 600)

        def _first_unread_from(who: str) -> MailEntry | None:
            for mid in mailbox.unread_ids(agent_name):
                e = mailbox.get(mid)
                if e is not None and e.sender == who:
                    return e
            return None

        # Forced yield: hand the event loop to the sender before we even look, so
        # a reply that's mid-flight in a concurrently-running peer gets a chance to
        # land first. This enforces a context switch to the agent we're waiting on.
        await asyncio.sleep(0)

        # Fast path: a reply from this sender already landed before we asked.
        entry = _first_unread_from(sender)
        if entry is None:
            # Otherwise wait for new mail to arrive, re-checking on each wakeup.
            channel = channel_bus.get_or_create(f"{agent_name}:messages")
            import time as _time
            deadline = _time.monotonic() + timeout
            while entry is None:
                remaining = deadline - _time.monotonic()
                if remaining <= 0:
                    break
                got = await channel.wait_for_message(timeout=remaining)
                if not got:
                    break
                # Drain the wakeup signal (content is in the mailbox, not the queue).
                await channel.receive(timeout=0)
                # Yield again so the sender can finish writing before we read.
                await asyncio.sleep(0)
                entry = _first_unread_from(sender)

        if entry is None:
            return {"content": [{"type": "text", "text": f"No reply from '{sender}' yet."}]}
        mailbox.mark_read(agent_name, entry.msg_id)
        if on_tool_call and entry.sender != "TipAgent":
            on_tool_call(agent_name, "message_received", {"from": entry.sender})
        return {"content": [{"type": "text", "text": render_mail(entry, mailbox)}]}

    # Queue of senders awaiting replies (FIFO) — used only by reply_only agents.
    pending_replies: list[str] = []

    _start_time = start_time or datetime.now()

    @tool(
        name="get_time",
        description=(
            "Get the current date/time and how long you have been running. "
            "Use this to track elapsed time and manage your time budget."
        ),
        input_schema={
            "type": "object",
            "properties": {},
            "required": [],
        },
    )
    async def get_time(input: dict[str, Any]) -> dict[str, Any]:
        now = datetime.now()
        elapsed = now - _start_time
        elapsed_mins = int(elapsed.total_seconds() // 60)
        elapsed_secs = int(elapsed.total_seconds() % 60)
        return {"content": [{"type": "text", "text": (
            f"Current time: {now.strftime('%Y-%m-%d %H:%M:%S')}\n"
            f"Started at:   {_start_time.strftime('%Y-%m-%d %H:%M:%S')}\n"
            f"Elapsed:      {elapsed_mins}m {elapsed_secs}s"
        )}]}

    tools_list = [send_message, get_time]
    if not reply_only_mode:
        # Mailbox pull tools + wait_for_reply (replaces the old check_messages).
        tools_list[1:1] = [
            list_recent_messages,
            list_all_unread_mail,
            see_last_unread_mail,
            get_messages_by_sender,
            get_thread,
            wait_for_reply,
        ]

    server = create_sdk_mcp_server(
        name="agent_messaging",
        version="1.0.0",
        tools=tools_list,
    )
    # Expose pending_replies for framework injection path to push senders
    # Wrap in a simple namespace since sdk server is a dict
    server["_pending_replies"] = pending_replies
    # Expose raw tool handlers (name -> async fn) for in-process testing.
    server["_tool_handlers"] = {t.name: t.handler for t in tools_list}
    return server
