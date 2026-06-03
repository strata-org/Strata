"""
In-process MCP tools for inter-agent messaging via ChannelBus.

Agents get `send_message`, `check_messages`, and `get_time` tools automatically,
letting them communicate with other agents and track time.
"""

from __future__ import annotations

import asyncio
import random
from collections.abc import Callable
from datetime import datetime
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from ._channels import ChannelBus, ChannelMessage


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
    Create an MCP server exposing send_message and check_messages tools
    bound to this agent's identity and the shared ChannelBus.
    """

    @tool(
        name="send_message",
        description=(
            "Send a message to another agent by name. The message will appear in their inbox. "
            "Use this to coordinate, request information, or respond to other agents."
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
            },
            "required": ["to", "message"],
        },
    )
    async def send_message(input: dict[str, Any]) -> dict[str, Any]:
        recipient = input["to"]
        message = input["message"]

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
        messages_channel = f"{physical_recipient}:messages"
        await channel_bus.send_to(messages_channel, sender=sender_display, payload=message)

        # Yield to event loop — gives recipient agent a chance to wake and process
        await asyncio.sleep(random.uniform(0.1, 0.7))

        # Only pop pending reply AFTER successful delivery
        if reply_only_mode and pending_replies and pending_replies[0] == recipient:
            pending_replies.pop(0)
        # Record telemetry
        if on_tool_call:
            on_tool_call(agent_name, "send_message", {"to": recipient})
        return {"content": [{"type": "text", "text": f"Message sent to '{recipient}' successfully."}]}

    @tool(
        name="check_messages",
        description=(
            "Read the next pending message from your inbox. "
            "Optionally specify a timeout to wait for a message to arrive. "
            "Default: 0.5s (quick check). Use longer timeout (e.g. 60) after sending "
            "a message to another agent and waiting for their reply."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "timeout": {
                    "type": "number",
                    "description": "Seconds to wait for a message. Default 0.5. Use 30-60 when waiting for a reply.",
                },
            },
            "required": [],
        },
    )
    async def check_messages(input: dict[str, Any]) -> dict[str, Any]:
        timeout = min(max(input.get("timeout", 0.5), 0.1), 300)
        messages_channel = f"{agent_name}:messages"
        channel = channel_bus.get_or_create(messages_channel)

        msg = await channel.receive(timeout=timeout)
        if msg is None:
            return {"content": [{"type": "text", "text": "No messages in your inbox."}]}

        # Track sender for reply() — add to queue (never TipAgent)
        if msg.sender != "TipAgent":
            pending_replies.append(msg.sender)

        # Record message_received in telemetry
        if on_tool_call:
            on_tool_call(agent_name, "message_received", {"from": msg.sender})

        return {"content": [{"type": "text", "text": f"[From {msg.sender}]: {msg.payload}"}]}

    # Queue of senders awaiting replies (FIFO)
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
        tools_list.insert(1, check_messages)

    server = create_sdk_mcp_server(
        name="agent_messaging",
        version="1.0.0",
        tools=tools_list,
    )
    # Expose pending_replies for framework injection path to push senders
    # Wrap in a simple namespace since sdk server is a dict
    server["_pending_replies"] = pending_replies
    return server
