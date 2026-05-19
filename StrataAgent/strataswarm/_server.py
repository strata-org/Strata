from __future__ import annotations

import asyncio
from pathlib import Path
from typing import Any

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

from ._backend import AgentBackend
from ._channels import ChannelBus
from ._types import AgentEvent, AgentSpec, AgentStatus
from ._tools import ToolSet


class AgentCreateRequest(BaseModel):
    name: str
    system_prompt: str
    prompt: str
    allowed_tools: list[str] = []
    disallowed_tools: list[str] = []
    max_turns: int | None = None
    max_budget_usd: float | None = None
    timeout_seconds: float | None = None


class SwarmDashboard:
    """
    Interactive dashboard for creating, running, and controlling agent swarms.

    Supports:
    - Creating agents with custom specs (tools, halting, prompts)
    - Running the swarm (Start)
    - Pausing / resuming all or individual agents
    - Cancelling the swarm
    - Viewing per-agent messages and cross-agent chitchat
    - Sending user feedback to any agent
    """

    def __init__(
        self,
        backend_factory: Any,
        host: str = "0.0.0.0",
        port: int = 8420,
    ) -> None:
        self._backend_factory = backend_factory
        self.host = host
        self.port = port
        self.app = FastAPI(title="StrataSwarm Dashboard")
        self._connections: list[WebSocket] = []
        self._event_history: dict[str, list[dict[str, Any]]] = {}
        self._all_messages: list[dict[str, Any]] = []
        self._swarm: Any = None
        self._swarm_task: asyncio.Task | None = None
        self._agent_specs: list[AgentCreateRequest] = []
        self._setup_routes()

    def _setup_routes(self) -> None:
        static_dir = Path(__file__).parent / "_static"

        @self.app.get("/")
        async def index() -> HTMLResponse:
            return HTMLResponse((static_dir / "index.html").read_text())

        @self.app.websocket("/ws")
        async def websocket_endpoint(ws: WebSocket) -> None:
            await ws.accept()
            self._connections.append(ws)
            await ws.send_json(self._get_full_state())
            try:
                while True:
                    data = await ws.receive_json()
                    try:
                        await self._handle_client_message(data)
                    except Exception as e:
                        await ws.send_json({"type": "error", "message": str(e)})
            except WebSocketDisconnect:
                self._connections.remove(ws)

        @self.app.get("/api/state")
        async def get_state() -> dict[str, Any]:
            return self._get_full_state()

        @self.app.post("/api/agents/add")
        async def add_agent(req: AgentCreateRequest) -> dict[str, str]:
            self._agent_specs.append(req)
            await self._broadcast({"type": "specs_updated", "specs": self._get_specs_list()})
            return {"status": "added", "name": req.name}

        @self.app.post("/api/agents/{name}/remove")
        async def remove_agent(name: str) -> dict[str, str]:
            self._agent_specs = [s for s in self._agent_specs if s.name != name]
            await self._broadcast({"type": "specs_updated", "specs": self._get_specs_list()})
            return {"status": "removed"}

        @self.app.post("/api/swarm/start")
        async def start_swarm() -> dict[str, str]:
            if self._swarm_task and not self._swarm_task.done():
                return {"status": "already_running"}
            await self._create_and_run_swarm()
            return {"status": "started"}

        @self.app.post("/api/swarm/pause_all")
        async def pause_all() -> dict[str, str]:
            if self._swarm:
                for name in self._swarm._nodes:
                    self._swarm.pause(name)
            return {"status": "paused_all"}

        @self.app.post("/api/swarm/resume_all")
        async def resume_all() -> dict[str, str]:
            if self._swarm:
                for name in self._swarm._nodes:
                    self._swarm.resume(name)
            return {"status": "resumed_all"}

        @self.app.post("/api/swarm/cancel")
        async def cancel_swarm() -> dict[str, str]:
            if self._swarm:
                self._swarm.cancel()
            return {"status": "cancelled"}

        @self.app.post("/api/swarm/create_new")
        async def create_new() -> dict[str, str]:
            if self._swarm_task and not self._swarm_task.done():
                self._swarm.cancel()
                await asyncio.sleep(0.5)
            self._swarm = None
            self._swarm_task = None
            self._agent_specs = []
            self._event_history = {}
            self._all_messages = []
            await self._broadcast({"type": "reset"})
            return {"status": "reset"}

        @self.app.post("/api/agents/{name}/pause")
        async def pause_agent(name: str) -> dict[str, str]:
            if self._swarm:
                self._swarm.pause(name)
            return {"status": "paused"}

        @self.app.post("/api/agents/{name}/resume")
        async def resume_agent(name: str) -> dict[str, str]:
            if self._swarm:
                self._swarm.resume(name)
            return {"status": "resumed"}

        @self.app.post("/api/agents/{name}/cancel")
        async def cancel_agent(name: str) -> dict[str, str]:
            if self._swarm:
                self._swarm.cancel_agent(name)
            return {"status": "cancelled"}

        @self.app.post("/api/agents/{name}/message")
        async def send_message_to_agent(name: str, body: dict[str, Any]) -> dict[str, str]:
            message = body.get("message", "")
            if self._swarm:
                await self._swarm.send_to_agent(name, sender="user", payload=message)
            return {"status": "sent"}

    async def _handle_client_message(self, data: dict[str, Any]) -> None:
        action = data.get("action")
        agent_name = data.get("agent")

        if action == "add_agent":
            try:
                req = AgentCreateRequest(**data.get("spec", {}))
                self._agent_specs.append(req)
                await self._broadcast({"type": "specs_updated", "specs": self._get_specs_list()})
            except Exception as e:
                await self._broadcast({"type": "error", "message": f"Failed to add agent: {e}"})

        elif action == "remove_agent" and agent_name:
            self._agent_specs = [s for s in self._agent_specs if s.name != agent_name]
            await self._broadcast({"type": "specs_updated", "specs": self._get_specs_list()})

        elif action == "start":
            if not self._swarm_task or self._swarm_task.done():
                await self._create_and_run_swarm()

        elif action == "pause_all":
            if self._swarm:
                for name in self._swarm._nodes:
                    self._swarm.pause(name)

        elif action == "resume_all":
            if self._swarm:
                for name in self._swarm._nodes:
                    self._swarm.resume(name)

        elif action == "cancel":
            if self._swarm:
                self._swarm.cancel()

        elif action == "create_new":
            if self._swarm_task and not self._swarm_task.done():
                self._swarm.cancel()
            self._swarm = None
            self._swarm_task = None
            self._agent_specs = []
            self._event_history = {}
            self._all_messages = []
            await self._broadcast({"type": "reset"})

        elif action == "pause" and agent_name:
            if self._swarm:
                self._swarm.pause(agent_name)

        elif action == "resume" and agent_name:
            if self._swarm:
                self._swarm.resume(agent_name)

        elif action == "cancel_agent" and agent_name:
            if self._swarm:
                self._swarm.cancel_agent(agent_name)

        elif action == "send_message" and agent_name:
            if self._swarm:
                await self._swarm.send_to_agent(
                    agent_name, sender="user", payload=data.get("message", "")
                )

    async def _create_and_run_swarm(self) -> None:
        from ._swarm import Swarm, ExecutionMode

        self._event_history = {}
        self._all_messages = []
        self._swarm = Swarm(
            backend_factory=self._backend_factory,
            enable_messaging=True,
            wait_after_completion=True,
        )

        for spec_req in self._agent_specs:
            tools = ToolSet()
            for t in spec_req.allowed_tools:
                tools.allow(t)
            for t in spec_req.disallowed_tools:
                tools.disallow(t)

            agent_spec = AgentSpec(
                name=spec_req.name,
                system_prompt=spec_req.system_prompt,
                prompt=spec_req.prompt,
                tools=tools,
                max_turns=spec_req.max_turns,
                max_budget_usd=spec_req.max_budget_usd,
                timeout_seconds=spec_req.timeout_seconds,
            )
            self._swarm.add(agent_spec)

        self._swarm.set_event_callback(self.on_agent_event)
        await self._broadcast({"type": "swarm_started", "agents": self._get_specs_list()})

        async def run_swarm():
            results = await self._swarm.run(mode=ExecutionMode.AWAIT_ALL)
            summary = {}
            for name, r in results.items():
                summary[name] = {
                    "status": r.status.value,
                    "halted_by": r.halted_by,
                    "cost_usd": r.cost_usd,
                    "num_turns": r.num_turns,
                }
            await self._broadcast({"type": "swarm_completed", "results": summary})

        self._swarm_task = asyncio.create_task(run_swarm())

    def _get_specs_list(self) -> list[dict[str, Any]]:
        return [s.model_dump() for s in self._agent_specs]

    def _get_full_state(self) -> dict[str, Any]:
        agents: dict[str, Any] = {}
        if self._swarm:
            for name, result in self._swarm.results.items():
                agents[name] = {
                    "name": name,
                    "status": result.status.value if hasattr(result.status, "value") else str(result.status),
                    "session_id": result.session_id,
                    "cost_usd": result.cost_usd,
                    "num_turns": result.num_turns,
                    "halted_by": result.halted_by,
                }
            for name in self._swarm._nodes:
                if name not in agents:
                    agents[name] = {"name": name, "status": "pending", "session_id": None}

        return {
            "agents": agents,
            "specs": self._get_specs_list(),
            "running": self._swarm_task is not None and not self._swarm_task.done(),
            "all_messages": self._all_messages[-200:],
        }

    async def on_agent_event(self, event: AgentEvent) -> None:
        if event.agent_name not in self._event_history:
            self._event_history[event.agent_name] = []

        entry = {
            "agent": event.agent_name,
            "event_type": event.event_type,
            "data": str(event.data) if event.data else None,
            "timestamp_ms": event.timestamp_ms,
        }
        self._event_history[event.agent_name].append(entry)

        if event.event_type == "message":
            self._all_messages.append(entry)

        payload = {"type": "agent_event", **entry}
        await self._broadcast(payload)

    async def _broadcast(self, payload: dict[str, Any]) -> None:
        for ws in list(self._connections):
            try:
                await ws.send_json(payload)
            except Exception:
                self._connections.remove(ws)

    async def start(self) -> None:
        import uvicorn

        config = uvicorn.Config(
            self.app, host=self.host, port=self.port, log_level="warning"
        )
        server = uvicorn.Server(config)
        asyncio.create_task(server.serve())
