"""
MCP tool for listing agents visible to the caller.

Provides a `list_agents` tool that returns the current roster of agents
the caller can communicate with, including dynamically spawned agents,
along with their descriptions and runtime status.
"""

from __future__ import annotations

import json
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool


def create_directory_server(agent_name: str, swarm: Any):
    """
    Create an MCP server exposing the list_agents tool,
    bound to the caller's identity and the swarm's visibility graph.
    """

    @tool(
        name="list_agents",
        description=(
            "List all agents you can communicate with, their descriptions, and current status. "
            "Use this to discover which agents are available and what they do."
        ),
        input_schema={
            "type": "object",
            "properties": {},
            "required": [],
        },
    )
    async def list_agents(input: dict[str, Any]) -> dict[str, Any]:
        visible = swarm._visibility_graph.get(agent_name, set())
        agents = []
        for name in sorted(visible):
            # Resolve node — for sharded agents, use first instance
            node = None
            if name in swarm._nodes:
                node = swarm._nodes[name]
            elif name in swarm._sharded_agents:
                instance_name = f"{name}_0"
                if instance_name in swarm._nodes:
                    node = swarm._nodes[instance_name]

            if node is None:
                continue

            description = node.spec.description or name

            # Determine agent status from results/tasks
            if name in swarm._results:
                status = swarm._results[name].status.value
            elif name in swarm._sharded_agents:
                # Sharded: running if any instance is running
                any_running = any(
                    f"{name}_{i}" in swarm._tasks and not swarm._tasks[f"{name}_{i}"].done()
                    for i in range(swarm._sharded_agents[name].replicas)
                )
                status = "running" if any_running else "completed"
            elif name in swarm._tasks:
                task = swarm._tasks[name]
                if task.done():
                    status = "completed"
                else:
                    status = "running"
            else:
                status = "pending"

            agents.append({
                "name": name,
                "description": description,
                "status": status,
            })

        text = json.dumps(agents, indent=2)
        return {"content": [{"type": "text", "text": text}]}

    return create_sdk_mcp_server(
        name="agent_directory",
        version="1.0.0",
        tools=[list_agents],
    )
