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
    route_message: Callable[[str, str], str] | None = None,
    get_sender_display: Callable[[str], str] | None = None,
    on_tool_call: Callable[[str, str, dict], None] | None = None,
    reply_only_mode: bool = False,
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
        if reply_only_mode:
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

        # Rewrite sender name for sharded instances (transparent to recipient)
        sender_display = get_sender_display(agent_name) if get_sender_display else agent_name
        # Route to physical instance if sharded (transparent to sender)
        physical_recipient = route_message(recipient, message) if route_message else recipient
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
            "Only call this AFTER you have been notified that messages are waiting. "
            "Do NOT call this in a loop to poll — the framework notifies you automatically."
        ),
        input_schema={
            "type": "object",
            "properties": {},
            "required": [],
        },
    )
    async def check_messages(input: dict[str, Any]) -> dict[str, Any]:
        messages_channel = f"{agent_name}:messages"
        channel = channel_bus.get_or_create(messages_channel)

        msg = await channel.receive(timeout=0.5)
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

    @tool(
        name="reply",
        description=(
            "Reply to the agent who last messaged you. You MUST use this instead of "
            "send_message when responding to a request. This ensures replies go to "
            "the correct requester in order. Only specify the message content."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "message": {
                    "type": "string",
                    "description": "Your reply message.",
                },
            },
            "required": ["message"],
        },
    )
    async def reply(input: dict[str, Any]) -> dict[str, Any]:
        message = input["message"]

        if not pending_replies:
            return {"content": [{"type": "text", "text":
                "ERROR: No pending message to reply to. Use send_message for unsolicited messages."}]}

        recipient = pending_replies.pop(0)
        sender_display = get_sender_display(agent_name) if get_sender_display else agent_name
        physical_recipient = route_message(recipient, message) if route_message else recipient
        messages_channel = f"{physical_recipient}:messages"
        await channel_bus.send_to(messages_channel, sender=sender_display, payload=message)
        if on_tool_call:
            on_tool_call(agent_name, "send_message", {"to": recipient})
        return {"content": [{"type": "text", "text": f"Reply sent to '{recipient}' successfully."}]}

    @tool(
        name="get_time",
        description=(
            "Get the current time. Use this to track how long operations take "
            "or to include timestamps in your messages."
        ),
        input_schema={
            "type": "object",
            "properties": {},
            "required": [],
        },
    )
    async def get_time(input: dict[str, Any]) -> dict[str, Any]:
        now = datetime.now()
        return {"content": [{"type": "text", "text": now.strftime("%Y-%m-%d %H:%M:%S")}]}

    server = create_sdk_mcp_server(
        name="agent_messaging",
        version="1.0.0",
        tools=[send_message, check_messages, reply, get_time],
    )
    # Expose pending_replies for framework injection path to push senders
    # Wrap in a simple namespace since sdk server is a dict
    server["_pending_replies"] = pending_replies
    return server
