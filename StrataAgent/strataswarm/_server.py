from __future__ import annotations

import asyncio
from pathlib import Path
from typing import Any

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse

from ._types import AgentEvent, AgentStatus


class SwarmDashboard:
    def __init__(self, swarm: Any, host: str = "0.0.0.0", port: int = 8420) -> None:
        self.swarm = swarm
        self.host = host
        self.port = port
        self.app = FastAPI(title="StrataSwarm Dashboard")
        self._connections: list[WebSocket] = []
        self._event_history: dict[str, list[dict[str, Any]]] = {}
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
            await ws.send_json(self._get_state_snapshot())
            try:
                while True:
                    data = await ws.receive_json()
                    await self._handle_client_message(data)
            except WebSocketDisconnect:
                self._connections.remove(ws)

        @self.app.get("/api/agents")
        async def list_agents() -> dict[str, Any]:
            return self._get_state_snapshot()

        @self.app.get("/api/agents/{name}/history")
        async def agent_history(name: str) -> list[dict[str, Any]]:
            return self._event_history.get(name, [])

        @self.app.post("/api/agents/{name}/pause")
        async def pause_agent(name: str) -> dict[str, str]:
            self.swarm.pause(name)
            return {"status": "paused"}

        @self.app.post("/api/agents/{name}/resume")
        async def resume_agent(name: str) -> dict[str, str]:
            self.swarm.resume(name)
            return {"status": "resumed"}

        @self.app.post("/api/agents/{name}/cancel")
        async def cancel_agent(name: str) -> dict[str, str]:
            self.swarm.cancel_agent(name)
            return {"status": "cancelled"}

        @self.app.post("/api/agents/{name}/message")
        async def send_message(name: str, body: dict[str, Any]) -> dict[str, str]:
            message = body.get("message", "")
            await self.swarm.send_to_agent(name, sender="user", payload=message)
            return {"status": "sent"}

    async def _handle_client_message(self, data: dict[str, Any]) -> None:
        action = data.get("action")
        agent_name = data.get("agent")

        if action == "pause" and agent_name:
            self.swarm.pause(agent_name)
        elif action == "resume" and agent_name:
            self.swarm.resume(agent_name)
        elif action == "cancel" and agent_name:
            self.swarm.cancel_agent(agent_name)
        elif action == "send_message" and agent_name:
            await self.swarm.send_to_agent(
                agent_name, sender="user", payload=data.get("message", "")
            )
        elif action == "cancel_all":
            self.swarm.cancel()

    def _get_state_snapshot(self) -> dict[str, Any]:
        agents: dict[str, Any] = {}
        for name, result in self.swarm.results.items():
            agents[name] = {
                "name": name,
                "status": result.status.value if hasattr(result.status, "value") else str(result.status),
                "session_id": result.session_id,
                "cost_usd": result.cost_usd,
                "num_turns": result.num_turns,
                "halted_by": result.halted_by,
            }
        for name in self.swarm._nodes:
            if name not in agents:
                agents[name] = {"name": name, "status": "pending", "session_id": None}
        return {"agents": agents}

    async def on_agent_event(self, event: AgentEvent) -> None:
        if event.agent_name not in self._event_history:
            self._event_history[event.agent_name] = []
        self._event_history[event.agent_name].append({
            "event_type": event.event_type,
            "data": str(event.data) if event.data else None,
            "timestamp_ms": event.timestamp_ms,
        })

        payload = {
            "type": "agent_event",
            "agent": event.agent_name,
            "event_type": event.event_type,
            "data": str(event.data) if event.data else None,
            "timestamp_ms": event.timestamp_ms,
        }
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
