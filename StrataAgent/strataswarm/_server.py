from __future__ import annotations

import asyncio
import logging
from pathlib import Path
from typing import Any

import yaml

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

from ._backend import AgentBackend
from ._channels import ChannelBus
from ._types import AgentEvent, AgentSpec, AgentStatus

SWARM_SAVE_DIR = Path(__file__).parent.parent / "temp"
CHAT_SAVE_DIR = SWARM_SAVE_DIR / "chats"
LOG_DIR = SWARM_SAVE_DIR

# Set up logging for all strataswarm modules (file + console)
LOG_DIR.mkdir(parents=True, exist_ok=True)
_fmt = logging.Formatter("%(asctime)s [%(name)s] %(message)s", datefmt="%H:%M:%S")
_file_handler = logging.FileHandler(LOG_DIR / "server.log", mode="a")
_file_handler.setFormatter(_fmt)
_console_handler = logging.StreamHandler()
_console_handler.setFormatter(_fmt)
_root_logger = logging.getLogger("strataswarm")
_root_logger.setLevel(logging.DEBUG)
_root_logger.addHandler(_file_handler)
_root_logger.addHandler(_console_handler)
logger = logging.getLogger("strataswarm.server")
logger.info("Logger initialized")
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
    is_super_agent: bool = False


class SwarmConfig(BaseModel):
    name: str
    agents: list[AgentCreateRequest]


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
        self._swarm_name: str = ""
        self._setup_routes()
        self._setup_middleware()

    def _setup_middleware(self) -> None:
        from starlette.middleware.base import BaseHTTPMiddleware
        from starlette.requests import Request

        class RequestLogger(BaseHTTPMiddleware):
            async def dispatch(self, request: Request, call_next):
                logger.info(f"HTTP {request.method} {request.url.path}")
                response = await call_next(request)
                return response

        self.app.add_middleware(RequestLogger)

    def _setup_routes(self) -> None:
        static_dir = Path(__file__).parent / "_static"

        @self.app.get("/")
        async def index() -> HTMLResponse:
            return HTMLResponse((static_dir / "index.html").read_text())

        @self.app.websocket("/ws")
        async def websocket_endpoint(ws: WebSocket) -> None:
            await ws.accept()
            self._connections.append(ws)
            logger.info("WebSocket client connected")
            await ws.send_json(self._get_full_state())
            try:
                while True:
                    data = await ws.receive_json()
                    action = data.get("action", "?")
                    logger.info(f"WS {action}")
                    try:
                        await self._handle_client_message(data, ws)
                    except Exception as e:
                        logger.error(f"Handler error ({action}): {e}")
                        await ws.send_json({"type": "error", "message": str(e)})
            except WebSocketDisconnect:
                self._connections.remove(ws)
                logger.info("WebSocket client disconnected")

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
            self._swarm_name = ""
            self._event_history = {}
            self._all_messages = []
            await self._broadcast({"type": "reset"})
            return {"status": "reset"}

        # --- Swarm save/load ---
        @self.app.get("/api/swarm/saved")
        async def list_saved() -> list[str]:
            SWARM_SAVE_DIR.mkdir(parents=True, exist_ok=True)
            return [f.stem for f in SWARM_SAVE_DIR.glob("*.yaml")]

        @self.app.post("/api/swarm/save")
        async def save_swarm(body: dict[str, Any]) -> dict[str, str]:
            name = body.get("name", "").strip()
            if not name:
                return {"status": "error", "message": "Name is required"}
            SWARM_SAVE_DIR.mkdir(parents=True, exist_ok=True)
            config = SwarmConfig(name=name, agents=self._agent_specs)
            path = SWARM_SAVE_DIR / f"{name}.yaml"
            path.write_text(yaml.dump(config.model_dump(), default_flow_style=False, sort_keys=False))
            return {"status": "saved", "path": str(path)}

        @self.app.post("/api/swarm/load")
        async def load_swarm(body: dict[str, Any]) -> dict[str, str]:
            name = body.get("name", "").strip()
            path = SWARM_SAVE_DIR / f"{name}.yaml"
            if not path.exists():
                return {"status": "error", "message": f"Not found: {name}"}
            config = SwarmConfig.model_validate(yaml.safe_load(path.read_text()))
            self._agent_specs = config.agents
            self._swarm_name = config.name
            await self._broadcast({"type": "specs_updated", "specs": self._get_specs_list()})
            await self._broadcast({"type": "swarm_loaded", "name": config.name})
            return {"status": "loaded", "name": config.name}

        @self.app.post("/api/swarm/delete_saved")
        async def delete_saved(body: dict[str, Any]) -> dict[str, str]:
            name = body.get("name", "").strip()
            path = SWARM_SAVE_DIR / f"{name}.yaml"
            if path.exists():
                path.unlink()
            return {"status": "deleted"}

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

    async def _handle_client_message(self, data: dict[str, Any], ws: WebSocket) -> None:
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
            self._swarm_name = ""
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

        elif action == "save_swarm":
            name = data.get("name", "").strip()
            if not name:
                await self._broadcast({"type": "error", "message": "Swarm name is required"})
                return
            SWARM_SAVE_DIR.mkdir(parents=True, exist_ok=True)
            config = SwarmConfig(name=name, agents=self._agent_specs)
            path = SWARM_SAVE_DIR / f"{name}.yaml"
            path.write_text(yaml.dump(config.model_dump(), default_flow_style=False, sort_keys=False))
            saved_list = [f.stem for f in SWARM_SAVE_DIR.glob("*.yaml")]
            await self._broadcast({"type": "swarm_saved", "name": name, "saved_list": saved_list})

        elif action == "load_swarm":
            name = data.get("name", "").strip()
            path = SWARM_SAVE_DIR / f"{name}.yaml"
            if not path.exists():
                await ws.send_json({"type": "error", "message": f"Swarm '{name}' not found"})
                return
            config = SwarmConfig.model_validate(yaml.safe_load(path.read_text()))
            self._agent_specs = config.agents
            self._swarm_name = config.name
            await ws.send_json({"type": "specs_updated", "specs": self._get_specs_list()})
            await ws.send_json({"type": "swarm_loaded", "name": config.name})

        elif action == "delete_swarm":
            name = data.get("name", "").strip()
            path = SWARM_SAVE_DIR / f"{name}.yaml"
            if path.exists():
                path.unlink()
            saved_list = [f.stem for f in SWARM_SAVE_DIR.glob("*.yaml")]
            await ws.send_json({"type": "swarm_deleted", "name": name, "saved_list": saved_list})

        elif action == "list_saved":
            SWARM_SAVE_DIR.mkdir(parents=True, exist_ok=True)
            saved_list = [f.stem for f in SWARM_SAVE_DIR.glob("*.yaml")]
            await ws.send_json({"type": "saved_list", "saved_list": saved_list})

        elif action == "save_chat":
            label = data.get("label", "").strip()
            filename = self._save_chat(label=label)
            if filename:
                await ws.send_json({"type": "chat_saved", "filename": filename})
            else:
                await ws.send_json({"type": "error", "message": "No chat to save"})

        elif action == "list_chats":
            CHAT_SAVE_DIR.mkdir(parents=True, exist_ok=True)
            chats = sorted(
                [f.stem for f in CHAT_SAVE_DIR.glob("*.yaml")],
                reverse=True,
            )
            await ws.send_json({"type": "chat_list", "chats": chats})

        elif action == "load_chat":
            name = data.get("name", "").strip()
            path = CHAT_SAVE_DIR / f"{name}.yaml"
            if not path.exists():
                await ws.send_json({"type": "error", "message": f"Chat '{name}' not found"})
                return
            chat_data = yaml.safe_load(path.read_text())
            await ws.send_json({"type": "chat_loaded", "chat": chat_data})

        elif action == "delete_chat":
            name = data.get("name", "").strip()
            path = CHAT_SAVE_DIR / f"{name}.yaml"
            if path.exists():
                path.unlink()
            chats = sorted(
                [f.stem for f in CHAT_SAVE_DIR.glob("*.yaml")],
                reverse=True,
            )
            await ws.send_json({"type": "chat_list", "chats": chats})

    async def _create_and_run_swarm(self) -> None:
        from ._swarm import Swarm, ExecutionMode

        self._event_history = {}
        self._all_messages = []
        swarm_name = self._swarm_name or "_".join(s.name for s in self._agent_specs[:3]) or "swarm"
        self._swarm_name = swarm_name
        # Project root is parent of StrataAgent (where relative paths in tool perms resolve)
        project_root = str(Path(__file__).parent.parent.parent)
        self._swarm = Swarm(
            backend_factory=self._backend_factory,
            enable_messaging=True,
            wait_after_completion=True,
            name=swarm_name,
            cwd=project_root,
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
                is_super_agent=spec_req.is_super_agent,
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
            for name, node in self._swarm._nodes.items():
                spawned_by = getattr(node.spec, "_spawned_by", None)
                if name not in agents:
                    # Determine status: check event history first, then task state
                    status = "pending"
                    if name in self._event_history:
                        # Find last status_change event
                        for evt in reversed(self._event_history[name]):
                            if evt.get("event_type") == "status_change" and evt.get("data"):
                                status = evt["data"]
                                break
                    elif name in self._swarm._tasks:
                        task = self._swarm._tasks[name]
                        status = "running" if not task.done() else "completed"
                    agents[name] = {"name": name, "status": status, "session_id": None, "spawned_by": spawned_by}
                else:
                    if spawned_by:
                        agents[name]["spawned_by"] = spawned_by
                # Include spec info for all running agents (including spawned)
                agents[name]["spec"] = {
                    "name": node.spec.name,
                    "system_prompt": node.spec.system_prompt or "",
                    "prompt": str(node.spec.prompt),
                    "allowed_tools": [t.to_claude_format() for t in node.spec.tools.allowed],
                    "disallowed_tools": [t.to_claude_format() for t in node.spec.tools.disallowed],
                    "max_turns": node.spec.max_turns,
                    "max_budget_usd": node.spec.max_budget_usd,
                    "timeout_seconds": node.spec.timeout_seconds,
                    "is_super_agent": node.spec.is_super_agent,
                    "spawned_by": spawned_by,
                }

        SWARM_SAVE_DIR.mkdir(parents=True, exist_ok=True)
        saved_list = [f.stem for f in SWARM_SAVE_DIR.glob("*.yaml")]

        # Per-agent message history (last 100 per agent)
        agent_messages: dict[str, list[dict[str, Any]]] = {}
        for agent_name, events in self._event_history.items():
            agent_messages[agent_name] = [
                e for e in events[-100:] if e.get("event_type") == "message"
            ]

        return {
            "agents": agents,
            "specs": self._get_specs_list(),
            "running": self._swarm_task is not None and not self._swarm_task.done(),
            "all_messages": self._all_messages[-200:],
            "agent_messages": agent_messages,
            "saved_list": saved_list,
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

    def _save_chat(self, label: str = "") -> str | None:
        """Save current chat history to a YAML file. Returns filename."""
        if not self._event_history and not self._all_messages:
            return None
        CHAT_SAVE_DIR.mkdir(parents=True, exist_ok=True)
        from datetime import datetime
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        swarm_name = ""
        if self._agent_specs:
            agents = "_".join(s.name for s in self._agent_specs[:3])
            swarm_name = f"_{agents}"
        if label:
            swarm_name = f"_{label}"
        filename = f"{timestamp}{swarm_name}.yaml"
        path = CHAT_SAVE_DIR / filename

        chat_data = {
            "timestamp": timestamp,
            "agents": [s.model_dump() for s in self._agent_specs],
            "messages": {},
            "all_messages": self._all_messages[-500:],
        }
        for agent_name, events in self._event_history.items():
            chat_data["messages"][agent_name] = events[-200:]

        path.write_text(yaml.dump(chat_data, default_flow_style=False, sort_keys=False, allow_unicode=True))
        return filename

    async def _broadcast(self, payload: dict[str, Any]) -> None:
        for ws in list(self._connections):
            try:
                await ws.send_json(payload)
            except Exception:
                self._connections.remove(ws)

    async def _heartbeat_loop(self) -> None:
        """Send periodic pings to keep WebSocket connections alive."""
        while True:
            await asyncio.sleep(10)
            for ws in list(self._connections):
                try:
                    await ws.send_json({"type": "ping"})
                except Exception:
                    self._connections.remove(ws)

    async def start(self) -> None:
        import uvicorn

        config = uvicorn.Config(
            self.app,
            host=self.host,
            port=self.port,
            log_level="warning",
            ws_ping_interval=30,
            ws_ping_timeout=600,
        )
        server = uvicorn.Server(config)
        asyncio.create_task(server.serve())
        asyncio.create_task(self._heartbeat_loop())
