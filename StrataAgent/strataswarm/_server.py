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
from ._types import AgentEvent, AgentSpec, AgentStatus, ShardConfig, Workspace

AGENT_SPECS_DIR = Path(__file__).parent / "agent_specs"
SWARM_SAVE_DIR = Path(__file__).parent / "temp"
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


class McpServerDef(BaseModel):
    command: str
    args: list[str] = []
    env: dict[str, str] = {}
    type: str = "stdio"


class AgentCreateRequest(BaseModel):
    name: str
    system_prompt: str = ""
    prompt: str = ""
    allowed_tools: list[str] = []
    disallowed_tools: list[str] = []
    model: str | None = None
    max_turns: int | None = None
    max_budget_usd: float | None = None
    timeout_seconds: float | None = None
    is_super_agent: bool = False
    reply_only: bool = False
    stateless: bool = False
    module: str | None = None
    checkpointable: bool = False
    checkpoint_prompt: str | None = None
    auto_start: bool = True
    mcp_servers: dict[str, McpServerDef] = {}
    workspace: dict[str, list[str]] | None = None
    description: str = ""
    visibility: str | dict = "all"
    child_prefix: str | None = None
    replicas: int | None = None
    routing: str | None = None
    routing_key: str | None = None
    max_inbound_length: int | None = None
    max_inbound_response: str | None = None
    max_outbound_length: int | None = None
    max_outbound_response: str | None = None


class SwarmConfig(BaseModel):
    name: str
    agents: list[AgentCreateRequest]
    nudge_module: str | None = None
    manager: str | None = None
    checkpoint: dict | None = None


def check_mcp_dependencies(agent_specs: list[AgentCreateRequest]) -> tuple[list[str], list[str]]:
    """Check external MCP server commands. Returns (errors, warnings)."""
    import shutil

    errors: list[str] = []
    warnings: list[str] = []
    checked: set[str] = set()

    for spec in agent_specs:
        for server_name, server_def in spec.mcp_servers.items():
            cmd = server_def.command
            if cmd in checked:
                continue
            checked.add(cmd)

            if not shutil.which(cmd):
                errors.append(
                    f"MCP server '{server_name}' (agent '{spec.name}') requires "
                    f"'{cmd}' but it is not installed or not in PATH."
                )

            # Check args for known tools that have secondary deps
            if cmd == "uvx" and server_def.args:
                package = server_def.args[0] if server_def.args else ""
                if package == "lean-lsp-mcp":
                    if not shutil.which("rg"):
                        warnings.append(
                            f"MCP server '{server_name}' (lean-lsp-mcp): 'ripgrep' (rg) "
                            f"not found. lean_local_search and some lean_verify features "
                            f"will be degraded."
                        )
    return errors, warnings


def _agent_request_from_raw(agent_raw: dict[str, Any], fallback_name: str) -> AgentCreateRequest:
    """Build an AgentCreateRequest from a decomposed agent YAML dict."""
    return AgentCreateRequest(
        name=agent_raw.get("name", fallback_name),
        system_prompt=agent_raw.get("system_prompt", ""),
        prompt=agent_raw.get("prompt", ""),
        allowed_tools=agent_raw.get("allowed_tools", []),
        disallowed_tools=agent_raw.get("disallowed_tools", []),
        model=agent_raw.get("model"),
        max_turns=agent_raw.get("max_turns"),
        max_budget_usd=agent_raw.get("max_budget_usd"),
        timeout_seconds=agent_raw.get("timeout_seconds"),
        is_super_agent=agent_raw.get("is_super_agent", False),
        reply_only=agent_raw.get("reply_only", False),
        stateless=agent_raw.get("stateless", False),
        module=agent_raw.get("module"),
        checkpointable=agent_raw.get("checkpointable", False),
        checkpoint_prompt=agent_raw.get("checkpoint_prompt"),
        auto_start=agent_raw.get("auto_start", True),
        mcp_servers={
            k: McpServerDef(**v) if isinstance(v, dict) else v
            for k, v in agent_raw.get("mcp_servers", {}).items()
        },
        workspace=agent_raw.get("workspace"),
        description=agent_raw.get("description", ""),
        visibility=agent_raw.get("visibility", "all"),
        replicas=agent_raw.get("replicas"),
        routing=agent_raw.get("routing"),
        routing_key=agent_raw.get("routing_key"),
        max_inbound_length=agent_raw.get("max_inbound_length"),
        max_inbound_response=agent_raw.get("max_inbound_response"),
        max_outbound_length=agent_raw.get("max_outbound_length"),
        max_outbound_response=agent_raw.get("max_outbound_response"),
    )


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
        port: int = 8421,
    ) -> None:
        self._backend_factory = backend_factory
        self.host = host
        self.port = port
        self.app = FastAPI(title="StrataSwarm v2 Dashboard")
        self._connections: list[WebSocket] = []
        self._event_history: dict[str, list[dict[str, Any]]] = {}
        self._all_messages: list[dict[str, Any]] = []
        self._swarm: Any = None
        self._swarm_task: asyncio.Task | None = None
        self._agent_specs: list[AgentCreateRequest] = []
        self._swarm_name: str = ""
        self._nudge_module: str | None = None
        self._manager: str | None = None
        self._agent_sessions: dict[str, str] = {}
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
                for name in self._swarm._registry.nodes:
                    self._swarm.pause(name)
            return {"status": "paused_all"}

        @self.app.post("/api/swarm/resume_all")
        async def resume_all() -> dict[str, str]:
            if self._swarm:
                for name in self._swarm._registry.nodes:
                    self._swarm.resume(name)
            return {"status": "resumed_all"}

        @self.app.post("/api/swarm/cancel")
        async def cancel_swarm() -> dict[str, str]:
            if self._swarm:
                self._swarm.cancel()
            return {"status": "cancelled"}

        @self.app.post("/api/swarm/checkpoint")
        async def create_checkpoint() -> dict[str, str]:
            if self._swarm and self._swarm._checkpoint_manager:
                path = self._swarm._checkpoint_manager.create(reason="user_request")
                return {"status": "created", "path": str(path)}
            return {"status": "error", "message": "No swarm or checkpointing disabled"}

        @self.app.get("/api/swarm/checkpoints")
        async def list_checkpoints() -> list[str]:
            if self._swarm and self._swarm._checkpoint_manager:
                return self._swarm._checkpoint_manager.list_checkpoints()
            # Fallback: check checkpoint dir directly (visible even without running swarm)
            cp_dir = SWARM_SAVE_DIR / "checkpoints"
            if cp_dir.exists():
                return sorted([d.name for d in cp_dir.iterdir() if d.is_dir()])
            return []

        @self.app.post("/api/swarm/resume_checkpoint")
        async def resume_checkpoint(body: dict[str, Any]) -> dict[str, str]:
            checkpoint_name = body.get("checkpoint", "")
            if not checkpoint_name:
                return {"status": "error", "message": "checkpoint name required"}
            if not self._swarm or not self._swarm._checkpoint_manager:
                return {"status": "error", "message": "no swarm or checkpointing disabled"}
            try:
                state = self._swarm._checkpoint_manager.restore(checkpoint_name)
                sessions = state.get("sessions", {})

                # Load per-agent checkpoint .md files for resume
                cp_dir = self._swarm._checkpoint_manager._dir / checkpoint_name / "agents"
                agent_checkpoints: dict[str, str] = {}
                if cp_dir.exists():
                    for f in cp_dir.glob("*.md"):
                        agent_checkpoints[f.stem] = f.read_text()

                chat_data = {
                    "swarm_name": state.get("swarm_name", "resumed"),
                    "agents": [s.model_dump() for s in self._agent_specs],
                    "sessions": sessions,
                    "agent_checkpoints": agent_checkpoints,
                }
                await self._resume_from_chat(chat_data)
                return {"status": "resumed", "from": checkpoint_name}
            except FileNotFoundError:
                return {"status": "error", "message": f"checkpoint '{checkpoint_name}' not found"}

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
            return [f.stem for f in AGENT_SPECS_DIR.glob("*.yaml")]

        @self.app.post("/api/swarm/save")
        async def save_swarm(body: dict[str, Any]) -> dict[str, str]:
            name = body.get("name", "").strip()
            if not name:
                return {"status": "error", "message": "Name is required"}
            AGENT_SPECS_DIR.mkdir(parents=True, exist_ok=True)
            config = SwarmConfig(name=name, agents=self._agent_specs)
            path = AGENT_SPECS_DIR / f"{name}.yaml"
            path.write_text(yaml.dump(config.model_dump(), default_flow_style=False, sort_keys=False))
            return {"status": "saved", "path": str(path)}

        @self.app.post("/api/swarm/load")
        async def load_swarm(body: dict[str, Any]) -> dict[str, str]:
            name = body.get("name", "").strip()
            path = AGENT_SPECS_DIR / f"{name}.yaml"
            if not path.exists():
                return {"status": "error", "message": f"Not found: {name}"}
            raw = yaml.safe_load(path.read_text())

            # Detect decomposed format: agents is a list of strings (names)
            agents_raw = raw.get("agents", [])
            if agents_raw and isinstance(agents_raw[0], str):
                # Decomposed: resolve each agent name from agents/ subdir
                agents_dir = AGENT_SPECS_DIR / "agents"
                agent_specs: list[AgentCreateRequest] = []
                for agent_name in agents_raw:
                    agent_path = agents_dir / f"{agent_name}.yaml"
                    if not agent_path.exists():
                        return {"status": "error", "message": f"Agent spec not found: {agent_name}"}
                    agent_raw = yaml.safe_load(agent_path.read_text())
                    agent_specs.append(_agent_request_from_raw(agent_raw, agent_name))
                self._agent_specs = agent_specs
                self._swarm_name = raw.get("name", name)
                self._nudge_module = raw.get("nudge_module")
                self._manager = raw.get("manager")
            else:
                # Legacy inline format
                config = SwarmConfig.model_validate(raw)
                self._agent_specs = config.agents
                self._swarm_name = config.name
                self._nudge_module = config.nudge_module
                self._manager = config.manager

            await self._broadcast({"type": "specs_updated", "specs": self._get_specs_list()})
            await self._broadcast({"type": "swarm_loaded", "name": self._swarm_name})
            return {"status": "loaded", "name": self._swarm_name}

        @self.app.post("/api/swarm/delete_saved")
        async def delete_saved(body: dict[str, Any]) -> dict[str, str]:
            name = body.get("name", "").strip()
            path = AGENT_SPECS_DIR / f"{name}.yaml"
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
            if self._swarm and hasattr(self._swarm, '_user_backend'):
                # Human typing = backend output. Inject with target so agent loop routes it.
                self._swarm._user_backend.inject_user_input(f"[to:{name}] {message}")
            return {"status": "sent"}

        @self.app.post("/api/agents/{name}/budget")
        async def increase_budget(name: str, body: dict[str, Any]) -> dict[str, str]:
            """Increase an agent's budget. Takes effect on next session reconnect.

            For a running agent, this updates the spec so that:
            - If the agent hits budget limit and retries, it reconnects with more budget
            - On checkpoint/resume, the new budget is used
            - The current live session's budget cannot be changed mid-flight (Claude limitation)
            """
            amount = body.get("amount", 0)
            if not self._swarm or name not in self._swarm._registry.nodes:
                return {"status": "error", "message": f"Agent '{name}' not found"}
            node = self._swarm._registry.nodes[name]
            old_budget = node.spec.max_budget_usd or 0
            node.spec.max_budget_usd = old_budget + amount
            # Also update the agent_specs list so checkpoint/save captures it
            for spec_req in self._agent_specs:
                if spec_req.name == name:
                    spec_req.max_budget_usd = node.spec.max_budget_usd
                    break
            return {
                "status": "ok",
                "agent": name,
                "old_budget": str(old_budget),
                "new_budget": str(node.spec.max_budget_usd),
                "note": "Takes effect on next reconnect/resume. Current session has its own budget.",
            }

        @self.app.post("/api/agents/{name}/interrupt")
        async def interrupt_agent_api(name: str, body: dict[str, Any]) -> dict[str, str]:
            """Interrupt an agent's current work via backend.interrupt() and send a message."""
            message = body.get("message", "User interrupted. Stop and wait for instructions.")
            if not self._swarm or name not in self._swarm._registry.nodes:
                return {"status": "error", "message": f"Agent '{name}' not found"}
            await self._swarm.interrupt_agent(name, message)
            return {"status": "ok", "agent": name}

        @self.app.get("/api/telemetry")
        async def get_telemetry() -> dict[str, Any]:
            """Return telemetry summary for all agents."""
            if not self._swarm:
                return {"agents": {}}
            import time as _time
            all_events = self._swarm._telemetry.get_all()
            summary: dict[str, Any] = {}
            for agent_name, events in all_events.items():
                tool_counts: dict[str, int] = {}
                message_sent_count = 0
                message_received_count = 0
                for ev in events:
                    if ev.event_type == "tool_call":
                        tool_counts[ev.tool_name or "unknown"] = tool_counts.get(ev.tool_name or "unknown", 0) + 1
                    elif ev.event_type == "message_sent":
                        message_sent_count += 1
                    elif ev.event_type == "message_received":
                        message_received_count += 1
                summary[agent_name] = {
                    "total_events": len(events),
                    "tool_calls": tool_counts,
                    "messages_sent": message_sent_count,
                    "messages_received": message_received_count,
                    "last_event_age_s": round(_time.time() - events[-1].timestamp, 1) if events else None,
                }
            return {"agents": summary}

        @self.app.get("/api/telemetry/{name}")
        async def get_agent_telemetry(name: str) -> dict[str, Any]:
            """Return detailed telemetry for a specific agent."""
            if not self._swarm:
                return {"events": []}
            events = self._swarm._telemetry.get_recent(name, n=100)
            return {
                "agent": name,
                "events": [
                    {
                        "type": ev.event_type,
                        "tool": ev.tool_name,
                        "target": ev.target,
                        "timestamp": ev.timestamp,
                        "success": ev.success,
                    }
                    for ev in events
                ],
            }

        @self.app.get("/api/nudges")
        async def get_nudge_history() -> dict[str, Any]:
            """Return nudge evaluation history (fired, skipped, errors)."""
            if not self._swarm:
                return {"history": [], "rules": []}
            history = self._swarm._nudge_monitor.get_history(limit=50)
            fire_counts = self._swarm._nudge_monitor._fire_counts
            rules = [
                {
                    "idx": i,
                    "name": fn.__name__,
                    "probability": prob,
                    "cooldown_s": cd,
                    "fire_count": fire_counts.get(i, 0),
                }
                for i, (fn, prob, cd) in enumerate(self._swarm._nudge_monitor._rules)
            ]
            return {"history": history, "rules": rules}

        @self.app.post("/api/mcp/restart")
        async def restart_mcp() -> dict[str, Any]:
            """Trigger domain-specific MCP restart via the nudge module hook."""
            if not self._swarm:
                return {"status": "error", "message": "No swarm running"}
            hook = self._swarm._nudge_monitor._on_mcp_restart
            if not hook:
                return {"status": "error", "message": "No ON_MCP_RESTART hook in nudge module"}
            try:
                result = await hook(self._swarm)
                return {"status": "restarted", "details": result}
            except Exception as e:
                logger.error(f"[MCP RESTART] Hook error: {e}")
                return {"status": "error", "message": str(e)}

        @self.app.get("/api/agents/{name}/state_machine")
        async def get_state_machine(name: str) -> dict[str, Any]:
            """Return the state machine definition and current state for a module agent."""
            if not self._swarm:
                return {"error": "No swarm running"}
            agent_instance = self._swarm._registry.agents.get(name)
            if not agent_instance:
                return {"error": f"Agent '{name}' not found or not running"}
            spec = self._swarm._registry.nodes[name].spec if name in self._swarm._registry.nodes else None
            if not spec or not spec.module:
                return {"error": f"Agent '{name}' is not a module agent"}

            # Import the module and extract TRANSITIONS
            import importlib
            try:
                mod = importlib.import_module(spec.module)
            except ImportError as e:
                return {"error": f"Cannot import module '{spec.module}': {e}"}

            transitions_raw = getattr(mod, "TRANSITIONS", None)
            if not transitions_raw:
                return {"error": f"Module '{spec.module}' has no TRANSITIONS table"}

            # Convert (state, transition) → next_state to serializable format
            transitions = [
                {"from": k[0], "transition": k[1], "to": v}
                for k, v in transitions_raw.items()
            ]

            # Extract states (all unique states mentioned)
            states = sorted(set(
                [t["from"] for t in transitions] + [t["to"] for t in transitions]
            ))

            # Get current workflow state
            workflow_state = getattr(agent_instance, '_workflow_state', None)
            current_state = None
            state_data = None
            if workflow_state:
                from dataclasses import asdict
                current_state = workflow_state.stage
                try:
                    state_data = asdict(workflow_state)
                except Exception:
                    state_data = {"stage": workflow_state.stage}

            return {
                "agent": name,
                "module": spec.module,
                "states": states,
                "transitions": transitions,
                "current_state": current_state,
                "state_data": state_data,
            }

        @self.app.get("/api/agents/live")
        async def get_live_agents() -> dict[str, Any]:
            """Return runtime state of all agents including spawned ones."""
            if not self._swarm:
                return {"agents": []}
            agents = []
            for name, node in self._swarm._registry.nodes.items():
                spec = node.spec
                # Build tools info
                allowed = spec.tools.to_claude_allowed() if spec.tools else []
                disallowed = spec.tools.to_claude_disallowed() if spec.tools else []
                # Workspace
                ws = None
                if spec.workspace:
                    ws = {
                        "read": spec.workspace.read,
                        "write": spec.workspace.write,
                        "edit": spec.workspace.edit,
                    }
                # Status from task + result
                status = "unknown"
                halted_by = None
                if name in self._swarm._registry.tasks:
                    task = self._swarm._registry.tasks[name]
                    if task.done():
                        # Task finished — check result for details
                        if name in self._swarm._registry.results:
                            r = self._swarm._registry.results[name]
                            halted_by = r.halted_by
                            if r.halted_by == "done_confirmed":
                                status = "done (confirmed)"
                            elif r.halted_by == "completion":
                                status = "completed"
                            elif r.halted_by:
                                status = f"stopped ({r.halted_by})"
                            else:
                                status = r.status.value if hasattr(r.status, "value") else "done"
                        else:
                            status = "done"
                    else:
                        # Check if it's exiting
                        if self._swarm._registry.exit_signals.get(name):
                            status = "exiting"
                        else:
                            status = "running"
                elif name in self._swarm._registry.results:
                    r = self._swarm._registry.results[name]
                    halted_by = r.halted_by
                    status = r.status.value if hasattr(r.status, "value") else str(r.status)
                else:
                    status = "pending"

                agents.append({
                    "name": name,
                    "status": status,
                    "halted_by": halted_by,
                    "is_super_agent": spec.is_super_agent,
                    "reply_only": spec.reply_only,
                    "spawned_by": getattr(spec, "_spawned_by", None),
                    "system_prompt": spec.system_prompt,
                    "prompt": spec.prompt[:500] if spec.prompt else None,
                    "allowed_tools": allowed,
                    "disallowed_tools": disallowed,
                    "workspace": ws,
                    "model": self._swarm._registry.models.get(name),
                    "cost_usd": self._swarm._registry.costs.get(name),
                    "session_id": self._swarm._registry.session_ids.get(name),
                })
            return {"agents": agents}

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
                for name in self._swarm._registry.nodes:
                    self._swarm.pause(name)

        elif action == "resume_all":
            if self._swarm:
                for name in self._swarm._registry.nodes:
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
            if self._swarm and hasattr(self._swarm, '_user_backend'):
                message = data.get("message", "")
                self._swarm._user_backend.inject_user_input(f"[to:{agent_name}] {message}")

        elif action == "save_swarm":
            name = data.get("name", "").strip()
            if not name:
                await self._broadcast({"type": "error", "message": "Swarm name is required"})
                return
            AGENT_SPECS_DIR.mkdir(parents=True, exist_ok=True)
            config = SwarmConfig(name=name, agents=self._agent_specs)
            path = AGENT_SPECS_DIR / f"{name}.yaml"
            path.write_text(yaml.dump(config.model_dump(), default_flow_style=False, sort_keys=False))
            saved_list = [f.stem for f in AGENT_SPECS_DIR.glob("*.yaml")]
            await self._broadcast({"type": "swarm_saved", "name": name, "saved_list": saved_list})

        elif action == "load_swarm":
            name = data.get("name", "").strip()
            path = AGENT_SPECS_DIR / f"{name}.yaml"
            if not path.exists():
                await ws.send_json({"type": "error", "message": f"Swarm '{name}' not found"})
                return
            raw = yaml.safe_load(path.read_text())
            agents_raw = raw.get("agents", [])
            if agents_raw and isinstance(agents_raw[0], str):
                agents_dir = AGENT_SPECS_DIR / "agents"
                agent_specs: list[AgentCreateRequest] = []
                for agent_name_str in agents_raw:
                    agent_path = agents_dir / f"{agent_name_str}.yaml"
                    if not agent_path.exists():
                        await ws.send_json({"type": "error", "message": f"Agent spec not found: {agent_name_str}"})
                        return
                    agent_raw = yaml.safe_load(agent_path.read_text())
                    agent_specs.append(_agent_request_from_raw(agent_raw, agent_name_str))
                self._agent_specs = agent_specs
                self._swarm_name = raw.get("name", name)
                self._nudge_module = raw.get("nudge_module")
                self._manager = raw.get("manager")
            else:
                config = SwarmConfig.model_validate(raw)
                self._agent_specs = config.agents
                self._swarm_name = config.name
                self._nudge_module = config.nudge_module
                self._manager = config.manager
            await ws.send_json({"type": "specs_updated", "specs": self._get_specs_list()})
            await ws.send_json({"type": "swarm_loaded", "name": self._swarm_name})

        elif action == "delete_swarm":
            name = data.get("name", "").strip()
            path = AGENT_SPECS_DIR / f"{name}.yaml"
            if path.exists():
                path.unlink()
            saved_list = [f.stem for f in AGENT_SPECS_DIR.glob("*.yaml")]
            await ws.send_json({"type": "swarm_deleted", "name": name, "saved_list": saved_list})

        elif action == "list_saved":
            AGENT_SPECS_DIR.mkdir(parents=True, exist_ok=True)
            saved_list = [f.stem for f in AGENT_SPECS_DIR.glob("*.yaml")]
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

        elif action == "resume_chat":
            name = data.get("name", "").strip()
            path = CHAT_SAVE_DIR / f"{name}.yaml"
            if not path.exists():
                await ws.send_json({"type": "error", "message": f"Chat '{name}' not found"})
                return
            chat_data = yaml.safe_load(path.read_text())
            await self._resume_from_chat(chat_data)
            await ws.send_json({"type": "swarm_resumed", "name": name})

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

    async def _resume_from_chat(self, chat_data: dict[str, Any]) -> None:
        """Resume a swarm from a saved chat using session IDs.
        Restores replicas, affinities, and session bindings."""
        from ._swarm import Swarm, ExecutionMode

        sessions = chat_data.get("sessions", {})
        agents_data = chat_data.get("agents", [])
        swarm_name = chat_data.get("swarm_name", "resumed")

        # Load agent specs from the saved chat
        self._agent_specs = [AgentCreateRequest(**a) for a in agents_data]
        self._swarm_name = swarm_name
        self._event_history = {}
        self._all_messages = []

        project_root = str(Path.cwd())
        self._swarm = Swarm(
            backend_factory=self._backend_factory,
            enable_messaging=True,
            wait_after_completion=True,
            name=swarm_name,
            cwd=project_root,
            checkpoint_dir=str(SWARM_SAVE_DIR / "checkpoints"),
            nudge_module=self._nudge_module,
            manager=self._manager,
        )

        for spec_req in self._agent_specs:
            tools = ToolSet()
            for t in spec_req.allowed_tools:
                tools.allow(t)
            for t in spec_req.disallowed_tools:
                tools.disallow(t)

            # Get session ID for this agent from saved chat
            session_id = sessions.get(spec_req.name)

            # Parse workspace and generate tool permissions from it
            ws_obj: Workspace | None = None
            if spec_req.workspace:
                ws_obj = Workspace(
                    read=spec_req.workspace.get("read", []),
                    write=spec_req.workspace.get("write", []),
                    edit=spec_req.workspace.get("edit", []),
                )
                for path in ws_obj.read:
                    tools.allow(f"Read({path})")
                for path in ws_obj.write:
                    tools.allow(f"Write({path})")
                for path in ws_obj.edit:
                    tools.allow(f"Edit({path})")

            # Convert MCP server defs
            external_mcp: dict[str, Any] = {}
            for server_name, server_def in spec_req.mcp_servers.items():
                config: dict[str, Any] = {"command": server_def.command}
                if server_def.args:
                    config["args"] = server_def.args
                if server_def.env:
                    config["env"] = server_def.env
                if server_def.type:
                    config["type"] = server_def.type
                external_mcp[server_name] = config

            # Build shard config if replicas requested
            shard_config: ShardConfig | None = None
            if spec_req.replicas and spec_req.replicas > 1:
                shard_config = ShardConfig(
                    replicas=spec_req.replicas,
                    routing=spec_req.routing or "round_robin",
                    routing_key=spec_req.routing_key,
                )

            agent_spec = AgentSpec(
                name=spec_req.name,
                system_prompt=spec_req.system_prompt,
                prompt=spec_req.prompt,
                tools=tools,
                model=spec_req.model,
                max_turns=spec_req.max_turns,
                max_budget_usd=spec_req.max_budget_usd,
                timeout_seconds=spec_req.timeout_seconds,
                is_super_agent=spec_req.is_super_agent,
                reply_only=spec_req.reply_only,
                resume_session_id=session_id,
                mcp_servers=external_mcp,
                workspace=ws_obj,
                description=spec_req.description,
                visibility=spec_req.visibility,
                child_prefix=spec_req.child_prefix,
                shard=shard_config,
                max_inbound_length=spec_req.max_inbound_length,
                max_inbound_response=spec_req.max_inbound_response,
                max_outbound_length=spec_req.max_outbound_length,
                max_outbound_response=spec_req.max_outbound_response,
            )

            if shard_config and shard_config.replicas > 1:
                from copy import copy
                for i in range(shard_config.replicas):
                    instance_spec = copy(agent_spec)
                    instance_spec.name = f"{spec_req.name}_{i}"
                    # Use per-instance session ID if available
                    instance_session = sessions.get(f"{spec_req.name}_{i}")
                    if instance_session:
                        instance_spec.resume_session_id = instance_session
                    self._swarm.add(instance_spec)
                self._swarm._registry.sharded_agents[spec_req.name] = shard_config
            else:
                self._swarm.add(agent_spec)

        # Restore affinities from checkpoint/saved state
        affinities = chat_data.get("agent_affinities", {})
        for key, physical in affinities.items():
            if ":" in key:
                sender, logical = key.split(":", 1)
                self._swarm._registry.affinities[(sender, logical)] = physical

        # Store per-agent checkpoint data for restore on run
        self._swarm._agent_checkpoints = chat_data.get("agent_checkpoints", {})

        self._swarm.set_event_callback(self.on_agent_event)
        await self._broadcast({"type": "swarm_started", "agents": self._get_specs_list()})

        async def run_swarm():
            try:
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
            except Exception as e:
                logger.error(f"[SWARM] run_swarm crashed: {e}")
                import traceback
                traceback.print_exc()
                await self._broadcast({"type": "error", "message": f"Swarm crashed: {e}"})

        self._swarm_task = asyncio.create_task(run_swarm())
        logger.info(f"Swarm resumed from chat with sessions: {sessions}")

    async def _create_and_run_swarm(self) -> None:
        from ._swarm import Swarm, ExecutionMode

        # Check MCP dependencies before starting
        dep_errors, dep_warnings = check_mcp_dependencies(self._agent_specs)
        if dep_errors:
            error_msg = "Cannot start swarm — missing dependencies:\n" + "\n".join(f"  • {e}" for e in dep_errors)
            logger.error(error_msg)
            await self._broadcast({"type": "error", "message": error_msg})
            return
        for w in dep_warnings:
            logger.warning(w)
            await self._broadcast({"type": "warning", "message": w})

        self._event_history = {}
        self._all_messages = []
        swarm_name = self._swarm_name or "_".join(s.name for s in self._agent_specs[:3]) or "swarm"
        self._swarm_name = swarm_name
        # Project root is parent of StrataAgent (where relative paths in tool perms resolve)
        project_root = str(Path.cwd())
        self._swarm = Swarm(
            backend_factory=self._backend_factory,
            enable_messaging=True,
            wait_after_completion=True,
            name=swarm_name,
            cwd=project_root,
            checkpoint_dir=str(SWARM_SAVE_DIR / "checkpoints"),
            nudge_module=self._nudge_module,
            manager=self._manager,
        )

        for spec_req in self._agent_specs:
            tools = ToolSet()
            for t in spec_req.allowed_tools:
                tools.allow(t)
            for t in spec_req.disallowed_tools:
                tools.disallow(t)

            # Parse workspace and generate tool permissions from it
            ws_obj: Workspace | None = None
            if spec_req.workspace:
                ws_obj = Workspace(
                    read=spec_req.workspace.get("read", []),
                    write=spec_req.workspace.get("write", []),
                    edit=spec_req.workspace.get("edit", []),
                )
                for path in ws_obj.read:
                    tools.allow(f"Read({path})")
                for path in ws_obj.write:
                    tools.allow(f"Write({path})")
                for path in ws_obj.edit:
                    tools.allow(f"Edit({path})")

            # Convert MCP server defs to the format Claude SDK expects
            external_mcp: dict[str, Any] = {}
            for server_name, server_def in spec_req.mcp_servers.items():
                config: dict[str, Any] = {"command": server_def.command}
                if server_def.args:
                    config["args"] = server_def.args
                if server_def.env:
                    config["env"] = server_def.env
                if server_def.type:
                    config["type"] = server_def.type
                external_mcp[server_name] = config

            # Build shard config if replicas requested
            shard_config: ShardConfig | None = None
            if spec_req.replicas and spec_req.replicas > 1:
                shard_config = ShardConfig(
                    replicas=spec_req.replicas,
                    routing=spec_req.routing or "round_robin",
                    routing_key=spec_req.routing_key,
                )

            agent_spec = AgentSpec(
                name=spec_req.name,
                system_prompt=spec_req.system_prompt,
                prompt=spec_req.prompt,
                tools=tools,
                model=spec_req.model,
                max_turns=spec_req.max_turns,
                max_budget_usd=spec_req.max_budget_usd,
                timeout_seconds=spec_req.timeout_seconds,
                is_super_agent=spec_req.is_super_agent,
                reply_only=spec_req.reply_only,
                stateless=spec_req.stateless,
                module=spec_req.module,
                checkpointable=spec_req.checkpointable,
                checkpoint_prompt=spec_req.checkpoint_prompt,
                auto_start=spec_req.auto_start,
                mcp_servers=external_mcp,
                workspace=ws_obj,
                description=spec_req.description,
                visibility=spec_req.visibility,
                child_prefix=spec_req.child_prefix,
                shard=shard_config,
                max_inbound_length=spec_req.max_inbound_length,
                max_inbound_response=spec_req.max_inbound_response,
                max_outbound_length=spec_req.max_outbound_length,
                max_outbound_response=spec_req.max_outbound_response,
            )

            if shard_config and shard_config.replicas > 1:
                from copy import copy

                for i in range(shard_config.replicas):
                    instance_spec = copy(agent_spec)
                    instance_spec.name = f"{spec_req.name}_{i}"
                    self._swarm.add(instance_spec)
                self._swarm._registry.sharded_agents[spec_req.name] = shard_config
            else:
                self._swarm.add(agent_spec)

        self._swarm.set_event_callback(self.on_agent_event)
        await self._broadcast({"type": "swarm_started", "agents": self._get_specs_list()})

        async def run_swarm():
            try:
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
            except Exception as e:
                logger.error(f"[SWARM] run_swarm crashed: {e}")
                import traceback
                traceback.print_exc()
                await self._broadcast({"type": "error", "message": f"Swarm crashed: {e}"})

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
                    "model": self._swarm._registry.models.get(name),
                }
            for name, node in self._swarm._registry.nodes.items():
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
                    elif name in self._swarm._registry.tasks:
                        task = self._swarm._registry.tasks[name]
                        status = "running" if not task.done() else "completed"
                    # Get last known cost from event history
                    last_cost = None
                    if name in self._event_history:
                        for evt in reversed(self._event_history[name]):
                            if evt.get("event_type") == "cost_update" and evt.get("data"):
                                try:
                                    last_cost = float(evt["data"])
                                except (ValueError, TypeError):
                                    pass
                                break
                    agents[name] = {"name": name, "status": status, "session_id": None, "cost_usd": last_cost, "spawned_by": spawned_by, "model": self._swarm._registry.models.get(name)}
                else:
                    if spawned_by:
                        agents[name]["spawned_by"] = spawned_by
                # Include spec info for all running agents (including spawned)
                agents[name]["spec"] = {
                    "name": node.spec.name,
                    "system_prompt": node.spec.system_prompt or "",
                    "prompt": str(node.spec.prompt),
                    "allowed_tools": [t.to_claude_format() for t in node.spec.tools.allowed] if node.spec.tools else [],
                    "disallowed_tools": [t.to_claude_format() for t in node.spec.tools.disallowed] if node.spec.tools else [],
                    "max_turns": node.spec.max_turns,
                    "max_budget_usd": node.spec.max_budget_usd,
                    "timeout_seconds": node.spec.timeout_seconds,
                    "is_super_agent": node.spec.is_super_agent,
                    "spawned_by": spawned_by,
                }

        AGENT_SPECS_DIR.mkdir(parents=True, exist_ok=True)
        saved_list = [f.stem for f in AGENT_SPECS_DIR.glob("*.yaml")]

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
        elif event.event_type == "session_id" and event.data:
            self._agent_sessions[event.agent_name] = str(event.data)

        payload = {"type": "agent_event", **entry}
        await self._broadcast(payload)

    def _save_chat(self, label: str = "") -> str | None:
        """Save current chat history to a YAML file with session IDs for resume."""
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

        # Collect session IDs from results + live tracking
        sessions: dict[str, str | None] = {}
        if self._swarm:
            for name, r in self._swarm.results.items():
                if r.session_id:
                    sessions[name] = r.session_id
        # Merge with any tracked from events
        sessions.update(self._agent_sessions)

        chat_data = {
            "timestamp": timestamp,
            "swarm_name": self._swarm_name,
            "agents": [s.model_dump() for s in self._agent_specs],
            "sessions": sessions,
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
