# Minimal stub of the icontract decorator surface so that imports
# in pyspec fixtures resolve. The Strata recognizer pattern-matches
# the decorator AST directly; runtime semantics here are irrelevant.

from typing import Any


def require(predicate: Any) -> Any:
    ...


def ensure(predicate: Any) -> Any:
    ...


def snapshot(capture: Any, name: str) -> Any:
    ...


def invariant(predicate: Any) -> Any:
    ...
