"""
In-process MCP tools for inter-agent messaging via ChannelBus.

Agents get `send_message`, `check_messages`, and `get_time` tools automatically,
letting them communicate with other agents and track time.
"""

from __future__ import annotations

import asyncio
from datetime import datetime
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from ._channels import ChannelBus, ChannelMessage


def create_messaging_server(
    agent_name: str,
    channel_bus: ChannelBus,
    known_agents: list[str],
):
    """
    Create an MCP server exposing send_message and check_messages tools
    bound to this agent's identity and the shared ChannelBus.
    """

    @tool(
        name="send_message",
        description=(
            "Send a message to another agent. The message will appear in their inbox. "
            f"Available agents: {', '.join(known_agents)}. "
            "Use this to coordinate, request information, or respond to other agents."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "to": {
                    "type": "string",
                    "description": f"Name of the recipient agent. One of: {', '.join(known_agents)}",
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

        if recipient not in known_agents:
            return {"content": [{"type": "text", "text": f"ERROR: Unknown agent '{recipient}'. Known agents: {', '.join(known_agents)}"}]}

        messages_channel = f"{recipient}:messages"
        await channel_bus.send_to(messages_channel, sender=agent_name, payload=message)
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

        return {"content": [{"type": "text", "text": f"[From {msg.sender}]: {msg.payload}"}]}

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

    return create_sdk_mcp_server(
        name="agent_messaging",
        version="1.0.0",
        tools=[send_message, check_messages, get_time],
    )
