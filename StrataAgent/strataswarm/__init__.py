"""StrataSwarm - Lightweight multi-agent orchestration for claude_agent_sdk."""

from ._agent import SwarmAgent
from ._backend import AgentBackend, BackendConfig, BackendMessage
from ._messaging import create_messaging_server
from ._channels import Channel, ChannelBus, ChannelMessage
from ._claude_backend import ClaudeBackend
from ._result_parsers import (
    CustomParser,
    JsonSchemaParser,
    PydanticFromTextParser,
    RawTextParser,
    RegexParser,
    ResultParser,
)
from ._server import SwarmDashboard
from ._swarm import AgentNode, ExecutionMode, Swarm
from ._templates import render_prompt
from ._tokens import CancellationToken, PauseToken
from ._tools import Tool, ToolSet
from ._types import AgentEvent, AgentResult, AgentSpec, AgentStatus, SwarmContext
from ._validators import (
    AllOf,
    AnyOf,
    ContainsText,
    HaltValidator,
    MessageCount,
    ResultFieldEquals,
    ResultFieldTruthy,
    ResultTextContains,
)

__all__ = [
    "AgentBackend",
    "AgentEvent",
    "AgentNode",
    "AgentResult",
    "AgentSpec",
    "AgentStatus",
    "AllOf",
    "AnyOf",
    "BackendConfig",
    "BackendMessage",
    "CancellationToken",
    "Channel",
    "ChannelBus",
    "ChannelMessage",
    "ClaudeBackend",
    "ContainsText",
    "create_messaging_server",
    "CustomParser",
    "ExecutionMode",
    "HaltValidator",
    "JsonSchemaParser",
    "MessageCount",
    "PauseToken",
    "PydanticFromTextParser",
    "RawTextParser",
    "RegexParser",
    "ResultFieldEquals",
    "ResultFieldTruthy",
    "ResultParser",
    "ResultTextContains",
    "Swarm",
    "SwarmAgent",
    "SwarmContext",
    "SwarmDashboard",
    "Tool",
    "ToolSet",
    "render_prompt",
]
