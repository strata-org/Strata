# StrataSwarm

A multi-agent framework for automated Lean 4 theorem proving. Agents are
deliberately constrained (limited tools, scoped file access, a visibility graph)
so they coordinate through proper channels instead of one context trying to do
everything. Built on top of `claude_agent_sdk`, but the framework layers
(visibility, messaging, workspace scoping, telemetry/nudges) are provider-agnostic.

The current proving engine is **PO v5** — a guide-centric proof orchestrator.

---

## Install

Drop StrataAgent into any Lean (lake) project and set it up with one command,
run from the **root of the target Lean project**:

```bash
curl -fsSL https://raw.githubusercontent.com/strata-org/Strata/amitayush/strata-agent/StrataAgent/clone_strata_agent.sh | bash
```

This downloads the `StrataAgent/` folder from GitHub, copies it into the current
project, wires up `lakefile.toml` (adds the `StrataAgent` lean_lib and the
`SwarmAgentTools` lean_exe), adds `StrataAgent/` to `.gitignore`, installs
`uv` + a venv, and runs `StrataAgent/setup.sh` (Python deps, ripgrep,
lean-lsp-mcp, itp-interface, the `SwarmAgentTools` Lean binary, and a standalone
Lean `repl` binary for `lean_multi_attempt`).

**lean_multi_attempt / repl** — `setup.sh` builds a standalone `repl` binary
under `StrataAgent/.repl` (matched to your project's Lean toolchain), without
adding `repl` as a project dependency — so it stays robust even when your
project's dependencies live outside `.lake/packages`. `start_dashboard.sh` then
exports `LEAN_REPL` / `LEAN_REPL_PATH` so lean-lsp-mcp enables
`lean_multi_attempt` automatically. If repl can't be built, everything else
still works — just without fast multi-attempt.

To copy from a local checkout instead of downloading:

```bash
./clone_strata_agent.sh /path/to/other-repo/StrataAgent
```

The point: you can add StrataAgent to any branch without merging the whole
`strataswarm` tree everywhere.

---

## Run

Start the dashboard with `start_dashboard.sh`:

```bash
./StrataAgent/start_dashboard.sh                       # port 8421, cheat sheet OFF
./StrataAgent/start_dashboard.sh --port 9000           # custom port
./StrataAgent/start_dashboard.sh --cheat-sheet path/to/Playbook.md   # enable a cheat sheet

# Start the dashboard AND kick off a proof — loads LeanSwarm, starts it,
# and sends the message to the TaskManager:
./StrataAgent/start_dashboard.sh --prompt "Prove the sorries in Strata/Transform/LoopElimCorrect.lean"
```

Runs in the foreground — press `Ctrl-C` to stop (frees the port). Then open
**http://localhost:8421**.

If the dashboard runs on a remote host, port-forward it to your laptop over SSH:

```bash
ssh -N -L 8421:localhost:8421 <this-host>
```

then open **http://localhost:8421** in your browser.

If you're running this over VS Code (connected to the remote host), it detects
the port automatically and shows a notification to forward it — just click
**Open in Browser** when the option appears, and it handles the tunneling for
you (no `ssh -L` needed).

Stop it:

```bash
./StrataAgent/kill_dashboard.sh          # default port 8421
./StrataAgent/kill_dashboard.sh 9000     # custom port
```

### Starting a proof from the dashboard

1. In the UI, **start** the `LeanSwarm` swarm (brings up `TaskManager` +
   `SearchAgent`).
2. Send a chat message to **TaskManager** naming the Lean file (and, optionally,
   specific theorem names). There is no structured form — you just describe the
   target in natural language, e.g. *"Prove the sorries in
   `Strata/Transform/LoopElimCorrect.lean`."*
3. `tm_clarifier` resolves your request to a concrete `theorem_file` +
   `theorem_names`, copies the file to `StrataAgent/Sandbox/Stub.lean`, and
   dispatches the prover. Watch progress in the UI (`tm_monitor` reports status).

---

## PO v5 — Guide-Centric Architecture

The core principle: **the guide is the single decision-maker** for a lemma
throughout its entire lifecycle. Every phase is *worker does a mechanical task →
guide reviews → guide decides*. There is no hard-coded `if/else` for strategy in
the orchestrator — every branch point goes through the guide.

- **`proof_guide`** is persistent and ephemeral at once: its knowledge lives in a
  `guide_state/<lemma>.md` file that survives destruction, crashes, and restarts.
  When context fills, it dumps to the `.md` and a fresh guide reads it back.
- **Workers are interchangeable** — the guide oversees them; they don't decide.

### The state machine

PO v5 (`modules/po_v5.py`, entry point `run_workflow`) drives a lemma through
these phases:

```
INIT → SELECT → PROVE → EXTRACT → DETECT → UPDATE → CHECK → ASSEMBLING → DONE
                  │                                    │
                  └── (guide: continue/decompose/      └── HAS_PENDING → SELECT
                       fresh_start/give_up)                 BLOCKED → FAILED
```

| Phase | What happens |
|-------|--------------|
| **INIT** | Split `Stub.lean` into defs/theorems, register root lemma(s) in the ledger. |
| **SELECT** | Guide picks the next pending child lemma to work on. |
| **PROVE** | `proof_writer` writes proof under guide's advice, looping until proved, `sorry` remains, or the guide changes strategy. |
| **EXTRACT** | `decl_extractor` factors leftover `sorry` helpers into separate files; guide reviews the decomposition. |
| **DETECT** | `cycle_checker` catches circular / duplicate lemmas (cheap structural compile check first, then soft matching); guide decides how to recover. |
| **UPDATE** | Mechanical bookkeeping — register new entries, resolve imports, propagate proved status upward. |
| **CHECK** | Root proved → assemble; pending work → select; stuck → guide decides unblock vs. give up. |
| **ASSEMBLING** | Copy proved stub into place, `compilation_fixer` resolves build errors under guide diagnosis. |

State is persisted (`_save_state`/`_load_state`) for crash/resume recovery; the
lemma ledger lives at `<workspace>/lemma_ledger.json`.

---

## The Agents

Agents are declared as YAML specs in `agent_specs/agents/*.yaml`. The swarm
(`agent_specs/swarm.yaml`, `name: LeanSwarm`) statically starts only
`TaskManager` and `SearchAgent`; everything else is created dynamically by the
workflow.

### Orchestration
| Agent | Role |
|-------|------|
| **TaskManager** | Central router / user interface. Parses the request, copies the target file to the sandbox, dispatches the prover, monitors, and reports. |
| **tm_clarifier** | Narrows a request to a concrete file + theorem name(s). |
| **tm_monitor** | Reads the workspace and reports proof progress to the user. |
| **tm_chat** | General Q&A about the codebase, Lean, or the system. |
| **prover_v5** | Runs the PO v5 workflow (`run_workflow`) over the sandbox. |

### Proof workers
| Agent | Role |
|-------|------|
| **proof_guide** | Sole decision-maker for a lemma. Advises writers, reviews all work, picks strategy. |
| **proof_writer** (`proof_writer_v2`) | Persistent writer. Replaces `sorry` with real proofs; file must always compile. |
| **proof_closer** | Leaf-node writer — must close ALL `sorry`, no decomposition allowed. |
| **decl_extractor** | Decomposes a Lean file, moving helper declarations into separate files. |
| **po_splitter** | Splits `Stub.lean` into definitions (`Stub/Def.lean`) and theorems. |
| **cycle_checker** | Detects circular / equivalent lemmas against the ledger. |
| **compilation_fixer** | Fixes Lean 4 build errors (duplicate defs, missing imports) during assembly. |
| **file_merger** | Merges preambles of two Lean files into one compilable file. |

### Services (always available)
| Agent | Role |
|-------|------|
| **SearchAgent** | Codebase search — finds definitions, lemmas, types. |
| **ProofLedger** | Tracks all proven lemmas across the swarm; writers consult it before starting. |
| **DeepProofValidator** | Validates proofs: compiles, no `sorry`, theorem signatures preserved. |
| **counter_example** | Checks lemma soundness by constructing counterexamples. |

---

## Framework internals

The `strataswarm/` package provides the coordination layer independent of PO v5:

```
strataswarm/
  _types.py         AgentSpec, AgentResult, AgentEvent, SwarmContext
  _tools.py         ToolSet (provider-agnostic allow/deny tools)
  _swarm.py         Swarm orchestrator (DAG, visibility graph, messaging)
  _agent.py         SwarmAgent (runs against AgentBackend, emits events)
  _backend.py       AgentBackend ABC   ·  _claude_backend.py  ClaudeBackend adapter
  _messaging.py     send_message / check_messages MCP tools (visibility-enforced)
  _directory.py     list_agents() MCP tool
  _spawn.py         Sub-agent spawning with scoped workspace permissions
  _channels.py      Channel / ChannelBus (with peek for notifications)
  _telemetry.py     Tool/message event stream   ·  _nudge.py  contextual nudges
  _checkpoint.py    Snapshot + resume
  _server.py        FastAPI + WebSocket dashboard   ·  _static/  UI
  run_dashboard.py  Dashboard entry point (--port)
  agent_specs/      YAML agent + swarm definitions
  modules/          PO v5 proof engine (po_v5.py, po_agents.py, task_manager.py, …)
```

Key ideas:

- **Visibility graph** — `send_message` is hard-enforced: an agent can only
  message agents in its visibility set. Not a prompt suggestion.
- **Scoped workspace** — when an agent spawns a child, the child gets exactly one
  file to edit and no Bash/Grep/Glob escape hatches. Isolation forces
  communication through SearchAgent / ProofValidator.
- **Telemetry + nudges** — every tool call and message is captured; rule-based,
  probabilistic reminders compensate for agents "forgetting" soft constraints as
  context grows.
- **Checkpoint / resume** — swarm state (sessions, files, ledger) is snapshotted
  so long runs survive crashes and timeouts.

### REST API (subset)

| Method | Endpoint | Description |
|--------|----------|-------------|
| POST | `/api/swarm/start` | Start the LeanSwarm config |
| POST | `/api/agents/{name}/message` | Send a chat message to an agent (`{"message": "..."}`) |
| POST | `/api/agents/{name}/{pause,resume,cancel,interrupt}` | Agent lifecycle controls |
| GET | `/api/agents` | List agents with status |
| GET | `/api/ledger/dag` | Lemma dependency DAG |
| POST | `/api/swarm/{checkpoint,resume_checkpoint,save,load,cancel}` | Swarm state |

### ClaudeBackend CLI path resolution

`ClaudeBackend()` resolves the Claude CLI path from `STRATA_AGENT_CLAUDE_PATH`,
else `~/.toolbox/bin/claude`. Override with `ClaudeBackend(cli_path="…")`.
