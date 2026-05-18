# StrataSwarm

Lightweight multi-agent orchestration framework wrapping `claude_agent_sdk` behind a provider-agnostic interface.

## Quickstart

### Install dependencies

```bash
cd StrataAgent
uv sync
```

### Multi-agent with messaging (agents talk to each other)

```python
import asyncio
from strataswarm import Swarm, AgentSpec, ToolSet, ExecutionMode, ClaudeBackend, SwarmDashboard

async def main():
    swarm = Swarm(backend_factory=lambda: ClaudeBackend())

    swarm.add(AgentSpec(
        name="researcher",
        system_prompt=(
            "You are the Researcher. You work with: writer (summarizes your findings). "
            "Find the data and send it to writer when ready."
        ),
        prompt="Read metrics.csv and find the highest revenue month. Send the result to writer.",
        tools=ToolSet().allow("Bash").allow("Read"),
        max_turns=10,
        timeout_seconds=60.0,
    ))

    swarm.add(AgentSpec(
        name="writer",
        system_prompt=(
            "You are the Writer. You work with: researcher (finds data for you). "
            "Wait for researcher to send you data, then write a summary."
        ),
        prompt="Wait for a message from researcher, then write a one-line summary to report.txt.",
        tools=ToolSet().allow("Bash"),
        max_turns=10,
        timeout_seconds=60.0,
    ))

    # Start dashboard (optional)
    dashboard = SwarmDashboard(swarm, port=8420)
    await dashboard.start()
    swarm.set_event_callback(dashboard.on_agent_event)

    results = await swarm.run(mode=ExecutionMode.AWAIT_ALL)
    total_cost = sum(r.cost_usd or 0 for r in results.values())
    print(f"Done. Total cost: ${total_cost:.4f}")

asyncio.run(main())
```

When `enable_messaging=True` (the default), each agent automatically gets:
- `send_message(to, message)` tool — send a message to another agent
- `check_messages(wait_seconds)` tool — read pending messages from other agents

The framework also injects notifications after each response if there are unread messages, nudging the agent to call `check_messages`.

### Single agent (no messaging)

```python
swarm = Swarm(backend_factory=lambda: ClaudeBackend(), enable_messaging=False)
swarm.add(AgentSpec(
    name="analyzer",
    prompt="Analyze main.py for bugs.",
    tools=ToolSet().allow("Read").allow("Bash"),
    max_turns=5,
))
```

### Structured output

```python
from pydantic import BaseModel
from strataswarm import JsonSchemaParser

class Result(BaseModel):
    score: int
    issues: list[str]

swarm.add(AgentSpec(
    name="reviewer",
    system_prompt="You are a code reviewer.",
    prompt="Review {{ file_path }} and report issues.",
    tools=ToolSet().allow("Read"),
    result_parser=JsonSchemaParser(output_type=Result),
    max_turns=5,
))
```

## Architecture

### Messaging channels (two channels per agent)

- `{agent_name}:inbox` — user/framework messages (injected directly into conversation)
- `{agent_name}:messages` — agent-to-agent messages (read via `check_messages` tool)

`send_message` writes to the recipient's `:messages` channel. After each response, the framework peeks at `:messages` — if pending, injects a notification like:
```
[NOTIFICATION]: You have 2 pending messages from: user_agent, noise_agent. Use check_messages to read them.
```

The agent then calls `check_messages` to consume them.

### System prompt requirement

When `enable_messaging=True`, every `AgentSpec` must have a `system_prompt`. The system prompt should describe:
- The agent's role
- Which other agents it works with and what they do

The framework appends messaging tool documentation as a postfix to the system prompt automatically.

### Module structure

```
strataswarm/
  __init__.py          Public exports
  _types.py            AgentSpec, AgentResult, AgentEvent, AgentStatus, SwarmContext
  _tools.py            ToolSet (provider-agnostic allowed/disallowed tools)
  _tokens.py           CancellationToken, PauseToken
  _channels.py         Channel, ChannelBus (with peek_summary for notifications)
  _validators.py       HaltValidator ABC (message-level + result-level halting)
  _result_parsers.py   ResultParser strategy: JsonSchema, Regex, Pydantic, Custom, Raw
  _templates.py        Jinja2 rendering (inline + file-based .j2)
  _backend.py          AgentBackend ABC (provider-agnostic LLM interface)
  _claude_backend.py   ClaudeBackend adapter (auto-resolves CLI path)
  _messaging.py        MCP tools for inter-agent messaging (send_message, check_messages)
  _agent.py            SwarmAgent (programs against AgentBackend, emits events before pause)
  _swarm.py            Swarm orchestrator (DAG, messaging injection, event callbacks)
  _server.py           FastAPI + WebSocket dashboard
  _static/index.html   Single-page dashboard UI
```

### ClaudeBackend CLI path resolution

`ClaudeBackend()` auto-resolves the Claude CLI path:
1. `STRATA_AGENT_CLAUDE_PATH` env var (if set)
2. `~/.toolbox/bin/claude` (default)

Override: `ClaudeBackend(cli_path="/custom/path/to/claude")`

## Dashboard

Start with:
```python
dashboard = SwarmDashboard(swarm, port=8420)
await dashboard.start()
swarm.set_event_callback(dashboard.on_agent_event)
```

Open `http://localhost:8420`.

### Features
- Agent sidebar with colored status badges
- Real-time message stream per agent
- Pause / Resume / Cancel controls
- Send user feedback to any running agent
- Session ID display (for manual CLI resume)
- Per-agent and total cost tracking

### REST API

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/agents` | List all agents with status |
| GET | `/api/agents/{name}/history` | Event history for an agent |
| POST | `/api/agents/{name}/pause` | Pause an agent |
| POST | `/api/agents/{name}/resume` | Resume a paused agent |
| POST | `/api/agents/{name}/cancel` | Cancel an agent |
| POST | `/api/agents/{name}/message` | Send user feedback (`{"message": "..."}`) |

## Halting conditions

Two evaluation points:
- `should_halt_on_messages(messages)` — checked per-message during streaming
- `should_halt_on_result(parsed_result, raw_result)` — checked after result parsing

```python
from strataswarm import ContainsText, ResultFieldTruthy, AnyOf

halt_when=AnyOf(validators=[
    ContainsText(text="error", case_sensitive=False),  # halt during streaming
    ResultFieldTruthy(field_name="has_errors"),         # halt after result parse
])
```

## Configuration

| `Swarm` param | Default | Description |
|---------------|---------|-------------|
| `backend_factory` | (required) | `Callable[[], AgentBackend]` — creates one backend per agent |
| `context` | `SwarmContext()` | Shared mutable state |
| `enable_messaging` | `True` | Auto-inject messaging tools and system prompt postfix |
