"""StrataSwarm headless benchmark runner.

A CLI that runs the swarm headless (no dashboard UI, no tm_monitor, no human-input
loop — just the prover + final deep validation) over many theorems in parallel,
isolating each concurrent proof in its own repository clone.

MVP scope (this module): YAML config, theorem discovery, clone sizing + shuffled
task planning, a SEQUENTIAL run loop with a pluggable per-attempt seam, and the
report format (per-lemma k/N confidence, time, cost, proof-file path, give-up
reasons). Parallel clone-pool scheduling layers on top of the same plan/report.

The interactive single-user dashboard is untouched — this is a separate entry.
"""
