"""Result records, cost/time extraction from Prover_v5 logs, and report writing.

Reported per attempt: status (proven | give_up | timeout | error), wall-time,
cost ($), the give-up reason (if any), and the path to the proof file. Aggregated
per lemma: k/N proved (a confidence signal), best time, total cost.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field, asdict
from pathlib import Path

from .plan import AttemptTask


@dataclass
class AttemptResult:
    lemma_key: str
    project: str
    file_rel: str
    theorem: str
    attempt_idx: int
    status: str                       # proven | give_up | timeout | error
    wall_s: float = 0.0
    cost_usd: float | None = None     # from the Prover_v5 "Finished: ... cost=$" line
    give_up_reason: str = ""
    proof_path: str = ""              # persisted Stub.lean when proven
    clone: str = ""                   # which clone/worker ran it
    detail: str = ""                  # free-form (error text, oracle detail)


# Prover_v5 emits: "[PO5] Finished: stage=done, ..., time=157.1min, cost=$129.48"
_FINISHED_RE = re.compile(r"Finished:.*?time=([\d.]+)min.*?cost=\$([\d.]+)")


def parse_prover_cost_time(prover_jsonl: Path) -> tuple[float | None, float | None]:
    """(cost_usd, minutes) from the LAST 'Finished:' line in a Prover_v5 log, or
    (None, None) if absent. Robust to mixed ts types / partial lines."""
    cost = minutes = None
    try:
        for line in prover_jsonl.read_text().splitlines():
            if "Finished:" not in line:
                continue
            try:
                data = str(json.loads(line).get("data", ""))
            except json.JSONDecodeError:
                data = line
            m = _FINISHED_RE.search(data)
            if m:
                minutes = float(m.group(1))
                cost = float(m.group(2))  # last one wins
    except OSError:
        pass
    return cost, minutes


def find_prover_log(session_dir: Path) -> Path | None:
    """Newest Prover_v5_*.jsonl under a session's LeanSwarm dir (or the dir itself)."""
    if not session_dir.exists():
        return None
    cands = sorted(session_dir.rglob("Prover_v5_*.jsonl"),
                   key=lambda p: p.stat().st_mtime, reverse=True)
    return cands[0] if cands else None


@dataclass
class LemmaSummary:
    lemma_key: str
    project: str
    file_rel: str
    theorem: str
    attempts: int
    proved: int                        # k in k/N
    best_wall_s: float | None = None
    total_cost_usd: float = 0.0
    proof_path: str = ""
    give_up_reasons: list[str] = field(default_factory=list)

    @property
    def confidence(self) -> str:
        return f"{self.proved}/{self.attempts}"


def summarize(results: list[AttemptResult]) -> list[LemmaSummary]:
    by_key: dict[str, list[AttemptResult]] = {}
    for r in results:
        by_key.setdefault(r.lemma_key, []).append(r)
    summaries = []
    for key, rs in by_key.items():
        r0 = rs[0]
        proved = [r for r in rs if r.status == "proven"]
        reasons = sorted({r.give_up_reason for r in rs
                          if r.status == "give_up" and r.give_up_reason})
        summaries.append(LemmaSummary(
            lemma_key=key, project=r0.project, file_rel=r0.file_rel,
            theorem=r0.theorem, attempts=len(rs), proved=len(proved),
            best_wall_s=min((r.wall_s for r in proved), default=None),
            total_cost_usd=round(sum((r.cost_usd or 0.0) for r in rs), 2),
            proof_path=next((r.proof_path for r in proved if r.proof_path), ""),
            give_up_reasons=reasons,
        ))
    summaries.sort(key=lambda s: (s.project, s.file_rel, s.theorem))
    return summaries


def write_report(report_dir: Path, results: list[AttemptResult]) -> Path:
    """Write attempts.jsonl + summary.jsonl + a human summary.txt. Returns the dir."""
    report_dir.mkdir(parents=True, exist_ok=True)
    (report_dir / "attempts.jsonl").write_text(
        "\n".join(json.dumps(asdict(r)) for r in results) + ("\n" if results else ""))

    summaries = summarize(results)
    (report_dir / "summary.jsonl").write_text(
        "\n".join(json.dumps({**asdict(s), "confidence": s.confidence}) for s in summaries)
        + ("\n" if summaries else ""))

    lines = ["StrataSwarm benchmark summary", "=" * 60, ""]
    total_cost = 0.0
    any_proved = 0
    for s in summaries:
        total_cost += s.total_cost_usd
        any_proved += 1 if s.proved > 0 else 0
        bt = f"{s.best_wall_s/60:.1f}min" if s.best_wall_s else "—"
        lines.append(f"[{s.confidence}] {s.project} :: {s.file_rel} :: {s.theorem}")
        lines.append(f"        best={bt}  cost=${s.total_cost_usd:.2f}  "
                     f"proof={s.proof_path or '—'}")
        for reason in s.give_up_reasons:
            lines.append(f"        give_up: {reason[:200]}")
    lines += ["", "-" * 60,
              f"lemmas: {len(summaries)}   proved (>=1 attempt): {any_proved}",
              f"total cost: ${total_cost:.2f}"]
    (report_dir / "summary.txt").write_text("\n".join(lines) + "\n")
    return report_dir
