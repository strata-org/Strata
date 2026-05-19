from __future__ import annotations

import asyncio
from collections.abc import Awaitable, Callable
from dataclasses import dataclass, field
from typing import Any

from ._agent import EventCallback, SwarmAgent
from ._backend import AgentBackend
from ._channels import ChannelBus
from ._messaging import create_messaging_server
from ._tokens import CancellationToken, PauseToken
from ._types import AgentEvent, AgentResult, AgentSpec, AgentStatus, SwarmContext


class ExecutionMode:
    AWAIT_ALL = "all"
    AWAIT_FIRST = "first"
    FIRE_FORGET = "forget"


@dataclass
class AgentNode:
    spec: AgentSpec[Any]
    depends_on: list[str] = field(default_factory=list)
    render_vars: dict[str, Any] = field(default_factory=dict)


class Swarm:
    def __init__(
        self,
        backend_factory: Callable[[], AgentBackend],
        context: SwarmContext | None = None,
        enable_messaging: bool = True,
        wait_after_completion: bool = False,
    ) -> None:
        self._nodes: dict[str, AgentNode] = {}
        self._results: dict[str, AgentResult[Any]] = {}
        self._tasks: dict[str, asyncio.Task[AgentResult[Any]]] = {}
        self._cancellation = CancellationToken()
        self._pause_tokens: dict[str, PauseToken] = {}
        self._channel_bus = ChannelBus()
        self._context = context or SwarmContext()
        self._backend_factory = backend_factory
        self._event_callback: EventCallback | None = None
        self._enable_messaging = enable_messaging
        self._wait_after_completion = wait_after_completion

    @property
    def context(self) -> SwarmContext:
        return self._context

    @property
    def channels(self) -> ChannelBus:
        return self._channel_bus

    @property
    def results(self) -> dict[str, AgentResult[Any]]:
        return dict(self._results)

    def set_event_callback(self, callback: EventCallback) -> None:
        self._event_callback = callback

    def add(
        self,
        spec: AgentSpec[Any],
        depends_on: list[str] | None = None,
        render_vars: dict[str, Any] | None = None,
    ) -> Swarm:
        if self._enable_messaging and not spec.system_prompt:
            raise ValueError(
                f"AgentSpec '{spec.name}' must have a system_prompt when messaging is enabled. "
                f"The system prompt should describe the agent's role and the other agents it can talk to."
            )
        node = AgentNode(
            spec=spec,
            depends_on=depends_on or [],
            render_vars=render_vars or {},
        )
        self._nodes[spec.name] = node
        self._pause_tokens[spec.name] = PauseToken()
        return self

    def cancel(self) -> None:
        self._cancellation.cancel()

    def cancel_agent(self, name: str) -> None:
        if name in self._tasks:
            self._tasks[name].cancel()

    def pause(self, agent_name: str) -> None:
        self._pause_tokens[agent_name].pause()

    def resume(self, agent_name: str) -> None:
        self._pause_tokens[agent_name].resume()

    async def send_to_agent(self, agent_name: str, sender: str, payload: Any) -> None:
        messages_channel = f"{agent_name}:messages"
        await self._channel_bus.send_to(messages_channel, sender=sender, payload=payload)

    def get_agent_session_id(self, agent_name: str) -> str | None:
        if agent_name in self._results:
            return self._results[agent_name].session_id
        return None

    async def _run_node(self, name: str) -> AgentResult[Any]:
        node = self._nodes[name]

        if node.depends_on:
            dep_tasks = [self._tasks[dep] for dep in node.depends_on if dep in self._tasks]
            if dep_tasks:
                await asyncio.gather(*dep_tasks, return_exceptions=True)
                for dep_name in node.depends_on:
                    if dep_name in self._results:
                        dep_result = self._results[dep_name]
                        if dep_result.halted_by == "cancelled":
                            result: AgentResult[Any] = AgentResult(
                                name=name, halted_by="dependency", status=AgentStatus.CANCELLED
                            )
                            self._results[name] = result
                            return result

        render_vars = dict(node.render_vars)
        for dep_name in node.depends_on:
            if dep_name in self._results:
                render_vars[dep_name] = self._results[dep_name]
        render_vars["context"] = await self._context.snapshot()

        backend = self._backend_factory()

        mcp_servers: dict[str, Any] | None = None
        combined_system_prompt: str | None = None

        if self._enable_messaging and len(self._nodes) > 1:
            other_agents = [n for n in self._nodes if n != name]
            messaging_server = create_messaging_server(
                agent_name=name,
                channel_bus=self._channel_bus,
                known_agents=other_agents,
            )
            mcp_servers = dict(node.spec.mcp_servers)
            mcp_servers["agent_messaging"] = messaging_server

            messaging_suffix = (
                f"\n\n=== MESSAGING ===\n"
                f"Your agent name is '{name}'.\n"
                f"You have tools to communicate with other agents:\n"
                f"- send_message(to, message): Send a message to another agent. "
                f"'to' must be one of: {', '.join(other_agents)}.\n"
                f"- check_messages(wait_seconds): Check your inbox for messages "
                f"from other agents or the user. Set wait_seconds (default 2) to "
                f"wait for a reply. Returns the next message or 'No messages'.\n\n"
                f"Messages you receive are tagged with the sender's identity.\n"
                f"================="
            )

            combined_system_prompt = node.spec.system_prompt + messaging_suffix
        else:
            combined_system_prompt = node.spec.system_prompt

        agent: SwarmAgent[Any] = SwarmAgent(
            spec=node.spec,
            backend=backend,
            channel_bus=self._channel_bus,
            cancellation=self._cancellation,
            pause=self._pause_tokens[name],
            render_vars=render_vars,
            on_event=self._event_callback,
            mcp_servers_override=mcp_servers,
            system_prompt_override=combined_system_prompt,
            wait_after_completion=self._wait_after_completion,
        )

        result = await agent.run()
        self._results[name] = result
        await self._context.set(f"result:{name}", result)
        return result

    async def run(self, mode: str = ExecutionMode.AWAIT_ALL) -> dict[str, AgentResult[Any]]:
        for name in self._nodes:
            task = asyncio.create_task(self._run_node(name), name=f"swarm:{name}")
            self._tasks[name] = task

        if mode == ExecutionMode.AWAIT_ALL:
            await asyncio.gather(*self._tasks.values(), return_exceptions=True)

        elif mode == ExecutionMode.AWAIT_FIRST:
            done, pending = await asyncio.wait(
                self._tasks.values(), return_when=asyncio.FIRST_COMPLETED
            )
            self._cancellation.cancel()
            for t in pending:
                t.cancel()
                try:
                    await t
                except asyncio.CancelledError:
                    pass

        elif mode == ExecutionMode.FIRE_FORGET:
            pass

        return dict(self._results)
