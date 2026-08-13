#!/usr/bin/env python3
"""CLI entry for the StrataSwarm headless benchmark runner.

    StrataAgent/.venv/bin/python StrataAgent/run_benchmark.py CONFIG.yaml
    StrataAgent/.venv/bin/python StrataAgent/run_benchmark.py CONFIG.yaml --dry-run
    StrataAgent/.venv/bin/python StrataAgent/run_benchmark.py CONFIG.yaml --plan-only

See bench/config.example.yaml for the config format. The interactive dashboard
(start_dashboard.sh) is unaffected — this is a separate, headless entry point.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Make `strataswarm` and `bench` importable regardless of CWD.
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from bench.runner import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
