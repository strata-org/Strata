# SI1 — ShrinkAudit follow-up

Read-only audit of `docs/historical/CoreToGOTO_ShrinkAudit.md` (2026-05-22)
against the current state of `htd/unstructured-to-goto` (HEAD ~ `d10422c2b`).

## Methodology

For each recommendation in `ShrinkAudit.md` I:

1. Located the targeted file/lemma/lines in the current tree.
2. Looked for cleanup commits that act on it (search `git log` for the
   file path and for keywords like "v1", "v2", "v3", "preservation
   combinator", "patcher lemmas", "OpDesc", "inj_subst", "_h_inj").
3. Read worker reports under `docs/_workers/*_report.md` (S1-S3, L1-L4,
   W1-W6, A1-A6) where they touch the audit's items.
4. Spot-checked the current state with `grep`/`wc` to verify whether
   the recommended change is in place, partial, or absent.

Status codes:

* **applied** — done; the recommendation is implemented.
* **partially applied** — some part landed; the residual is identified.
* **superseded** — file or design moved; recommendation no longer fits.
* **still actionable** — not done; could be done now.
* **declined** — investigated and decided against.

## 1. Per-recommendation status table

(filled in below)

## 2. What's still actionable

(filled in below)

## 3. Anything the audit missed

(filled in below)

## 4. Verdict

(filled in below)
