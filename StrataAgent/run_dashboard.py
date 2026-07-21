"""Thin wrapper — delegates to strataswarm/run_dashboard.py (the canonical entry).

Kept so `python StrataAgent/run_dashboard.py ...` keeps working. All flags
(--port, --no-cheat-sheet, --cheat-sheet PATH) are handled by the real module.
"""

import runpy
import sys
from pathlib import Path

_REAL = Path(__file__).parent / "strataswarm" / "run_dashboard.py"

if __name__ == "__main__":
    # Make `strataswarm` importable, then run the real script as __main__
    sys.path.insert(0, str(Path(__file__).parent))
    runpy.run_path(str(_REAL), run_name="__main__")
