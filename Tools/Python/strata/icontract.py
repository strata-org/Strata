#!/usr/bin/env python3
"""
Convert icontract-decorated Python files to Lean source constructing
Strata.Python.Specs.Signature values.

Maps:
  @icontract.require(lambda ...: cond) → preconditions (Assertion with SpecExpr)
  @icontract.ensure(lambda ...: cond)  → postconditions (SpecExpr)
  Type annotations                     → SpecType / SpecAtomType
  Functions                            → Signature.functionDecl
  Classes with methods                 → Signature.classDef

Lambda bodies are mapped to SpecExpr where possible:
  isinstance(x, T)       → .isInstanceOf (.var "x") "T"
  len(x) >= N            → .intGe (.len (.var "x")) (.intLit N)
  len(x) <= N            → .intLe (.len (.var "x")) (.intLit N)
  x >= N                 → .intGe (.var "x") (.intLit N)
  x <= N                 → .intLe (.var "x") (.intLit N)
  x >= F (float)         → .floatGe (.var "x") (.floatLit "F")
  x <= F (float)         → .floatLe (.var "x") (.floatLit "F")
  Other expressions      → .placeholder (original preserved in message)

Usage:
    python icontract_to_strata.py <input_file_or_dir> <output_dir>
"""

import ast
import sys
import os
import argparse
from pathlib import Path
from typing import Optional, Union


# ---------------------------------------------------------------------------
# Type annotation → Lean SpecType
# ---------------------------------------------------------------------------

# Map Python builtin type names to PythonIdent Lean constructors
BUILTIN_TYPE_MAP = {
    "int": ".builtinsInt",
    "float": ".builtinsFloat",
    "str": ".builtinsStr",
    "bool": ".builtinsBool",
    "bytes": ".builtinsBytes",
    "bytearray": ".builtinsBytearray",
    "complex": ".builtinsComplex",
    "dict": ".builtinsDict",
}

# Map typing module generics
TYPING_MAP = {
    "List": ".typingList",
    "Dict": ".typingDict",
    "Sequence": ".typingSequence",
    "Mapping": ".typingMapping",
    "Any": ".typingAny",
    "Union": ".typingUnion",
    "Literal": ".typingLiteral",
    "Generator": ".typingGenerator",
}


def type_annotation_to_lean(node: Optional[ast.expr], module_name: str = "") -> str:
    """Convert a Python type annotation AST node to a Lean SpecType expression."""
    if node is None:
        return "SpecType.ident .none .typingAny"

    if isinstance(node, ast.Constant):
        if node.value is None:
            return "SpecType.ofAtom .none .noneType"
        if isinstance(node.value, str):
            # Forward reference as string
            return f'SpecType.pyClass .none "{node.value}" #[]'
        return "SpecType.ident .none .typingAny"

    if isinstance(node, ast.Name):
        name = node.id
        if name == "None" or name == "NoneType":
            return "SpecType.ofAtom .none .noneType"
        if name in BUILTIN_TYPE_MAP:
            return f"SpecType.ident .none {BUILTIN_TYPE_MAP[name]}"
        if name in TYPING_MAP:
            return f"SpecType.ident .none {TYPING_MAP[name]}"
        # User-defined class
        return f'SpecType.pyClass .none "{name}" #[]'

    if isinstance(node, ast.Attribute):
        # e.g., typing.List, _datetime.date
        full = ast.unparse(node)
        # Check for typing.X
        if isinstance(node.value, ast.Name):
            if node.value.id == "typing" and node.attr in TYPING_MAP:
                return f"SpecType.ident .none {TYPING_MAP[node.attr]}"
        # External type reference
        return f'SpecType.pyClass .none "{full}" #[]'

    if isinstance(node, ast.Subscript):
        # e.g., List[int], Dict[str, int], Union[int, str], Optional[int]
        base = node.value
        base_name = ""
        if isinstance(base, ast.Name):
            base_name = base.id
        elif isinstance(base, ast.Attribute):
            if isinstance(base.value, ast.Name):
                base_name = base.attr

        if base_name == "Optional":
            # Optional[T] = Union[T, None]
            inner = type_annotation_to_lean(node.slice, module_name)
            return f"SpecType.union .none {inner} (SpecType.ofAtom .none .noneType)"

        if base_name == "Union":
            if isinstance(node.slice, ast.Tuple):
                parts = [type_annotation_to_lean(e, module_name) for e in node.slice.elts]
                if len(parts) == 0:
                    return "SpecType.ident .none .typingAny"
                result = parts[0]
                for p in parts[1:]:
                    result = f"SpecType.union .none ({result}) ({p})"
                return result
            return type_annotation_to_lean(node.slice, module_name)

        if base_name in ("List", "Sequence"):
            ident = TYPING_MAP[base_name]
            inner = type_annotation_to_lean(node.slice, module_name)
            return f"SpecType.ident .none {ident} #[{inner}]"

        if base_name in ("Dict", "Mapping"):
            ident = TYPING_MAP[base_name]
            if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 2:
                k = type_annotation_to_lean(node.slice.elts[0], module_name)
                v = type_annotation_to_lean(node.slice.elts[1], module_name)
                return f"SpecType.ident .none {ident} #[{k}, {v}]"
            return f"SpecType.ident .none {ident}"

        if base_name == "Literal":
            # Literal["a", "b"] or Literal[1, 2]
            if isinstance(node.slice, ast.Tuple):
                atoms = [_literal_to_atom(e) for e in node.slice.elts]
            else:
                atoms = [_literal_to_atom(node.slice)]
            atoms_str = ", ".join(atoms)
            return f"SpecType.ofArray .none #[{atoms_str}]"

        if base_name == "Generator":
            ident = TYPING_MAP["Generator"]
            if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 3:
                args = [type_annotation_to_lean(e, module_name) for e in node.slice.elts]
                return f"SpecType.ident .none {ident} #[{', '.join(args)}]"
            return f"SpecType.ident .none {ident}"

        # Fallback for parameterized types
        return f'SpecType.pyClass .none "{ast.unparse(node)}" #[]'

    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        # X | Y union syntax (Python 3.10+)
        left = type_annotation_to_lean(node.left, module_name)
        right = type_annotation_to_lean(node.right, module_name)
        return f"SpecType.union .none ({left}) ({right})"

    # Fallback
    return f'SpecType.pyClass .none "{ast.unparse(node)}" #[]'


def _literal_to_atom(node: ast.expr) -> str:
    if isinstance(node, ast.Constant):
        if isinstance(node.value, int):
            if node.value < 0:
                return f".intLiteral ({node.value})"
            return f".intLiteral {node.value}"
        if isinstance(node.value, str):
            return f'.stringLiteral "{_escape_lean_str(node.value)}"'
    return f'.stringLiteral "{_escape_lean_str(ast.unparse(node))}"'


def _escape_lean_str(s: str) -> str:
    """Escape a string for Lean string literals."""
    return s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")



# ---------------------------------------------------------------------------
# Lambda body → Lean SpecExpr
# ---------------------------------------------------------------------------

def expr_to_spec_expr(node: ast.expr, params: list[str]) -> str:
    """Convert a Python expression AST node to a Lean SpecExpr.

    Handles the patterns that Strata's SpecExpr supports:
      isinstance(x, T)  → .isInstanceOf
      len(x) >= N        → .intGe (.len ..) (.intLit N)
      x >= N             → .intGe / .floatGe
      x <= N             → .intLe / .floatLe
      0 <= x             → .intGe (.var "x") (.intLit 0)
      variable refs      → .var "name"

    Falls back to .placeholder for anything else.
    """
    # isinstance(subject, TypeName)
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name) and node.func.id == "isinstance":
            if len(node.args) == 2:
                subj = _expr_to_subject(node.args[0])
                type_name = _extract_type_name(node.args[1])
                if subj and type_name:
                    return f'.isInstanceOf {subj} "{type_name}"'

        # len(x) as standalone — not a comparison, just the call
        if isinstance(node.func, ast.Name) and node.func.id == "len":
            if len(node.args) == 1:
                subj = _expr_to_subject(node.args[0])
                if subj:
                    return f".len {subj}"

        # all(expr for var in iterable) → .forallList
        if isinstance(node.func, ast.Name) and node.func.id == "all":
            if len(node.args) == 1:
                result = _try_forall_list(node.args[0], params)
                if result:
                    return result

    # Comparisons: x >= N, x <= N, len(x) >= N, N <= x <= M (chained)
    if isinstance(node, ast.Compare):
        return _compare_to_spec_expr(node, params)

    # BoolOp: and / or
    if isinstance(node, ast.BoolOp):
        if isinstance(node.op, ast.Or):
            # Could be enum pattern: x == "A" or x == "B"
            enum_result = _try_enum_pattern(node)
            if enum_result:
                return enum_result

    # UnaryOp: not x
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        inner = expr_to_spec_expr(node.operand, params)
        if inner != ".placeholder":
            return f".not ({inner})"

    # Simple variable reference
    if isinstance(node, ast.Name):
        return f'.var "{node.id}"'

    return ".placeholder"


def _try_forall_list(node: ast.expr, params: list[str]) -> Optional[str]:
    """Try to translate all(expr for var in iterable) → .forallList.

    Handles:
      all(isinstance(e, int) for e in a)
      all(e >= 0 for e in data)
      all(e <= 100 for e in data)
      all(cond1 and cond2 for e in a) — splits and takes first translatable
    """
    if not isinstance(node, ast.GeneratorExp):
        return None
    if len(node.generators) != 1:
        return None
    gen = node.generators[0]
    if gen.ifs:  # We don't handle filtered generators yet
        return None

    # Extract loop variable name
    if not isinstance(gen.target, ast.Name):
        return None
    var_name = gen.target.id

    # Extract iterable as subject
    iter_subj = _expr_to_subject(gen.iter)
    if not iter_subj:
        return None

    # Translate the body expression with the loop var in scope
    body_params = params + [var_name]
    body_expr = expr_to_spec_expr(node.elt, body_params)
    if body_expr != ".placeholder":
        return f'.forallList {iter_subj} "{var_name}" ({body_expr})'

    # If body is an 'and' chain, try splitting and wrapping each part
    # as a separate forallList (take the first one that works)
    if isinstance(node.elt, ast.BoolOp) and isinstance(node.elt.op, ast.And):
        # Try to translate each conjunct; if ALL translate, we could
        # emit multiple forallLists, but SpecExpr doesn't have 'and'.
        # Just try the first translatable one for now.
        for val in node.elt.values:
            sub = expr_to_spec_expr(val, body_params)
            if sub != ".placeholder":
                return f'.forallList {iter_subj} "{var_name}" ({sub})'

    return None


def _expr_to_subject(node: ast.expr) -> Optional[str]:
    """Convert an expression to a SpecExpr subject (for use in comparisons etc.)."""
    if isinstance(node, ast.Name):
        return f'(.var "{node.id}")'

    if isinstance(node, ast.Subscript):
        # x["field"] or x[0]
        subj = _expr_to_subject(node.value)
        if subj and isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, str):
            return f'(.getIndex {subj} "{_escape_lean_str(node.slice.value)}")'
        return None

    if isinstance(node, ast.Attribute):
        # result.attr → getIndex
        subj = _expr_to_subject(node.value)
        if subj:
            return f'(.getIndex {subj} "{node.attr}")'
        return None

    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1:
            inner = _expr_to_subject(node.args[0])
            if inner:
                return f"(.len {inner})"
        return None

    if isinstance(node, ast.BinOp):
        left = _expr_to_subject(node.left)
        right = _expr_to_subject(node.right)
        if left and right:
            if isinstance(node.op, ast.Add):
                return f"(.intAdd {left} {right})"
            if isinstance(node.op, ast.Sub):
                return f"(.intSub {left} {right})"
            if isinstance(node.op, ast.Mult):
                return f"(.intMul {left} {right})"
        return None

    return None


def _extract_type_name(node: ast.expr) -> Optional[str]:
    """Extract a type name string from an isinstance second argument."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return ast.unparse(node)
    if isinstance(node, ast.Tuple):
        # isinstance(x, (int, float)) — take first for simplicity
        if node.elts:
            return _extract_type_name(node.elts[0])
    return None


def _int_literal(node: ast.expr) -> Optional[str]:
    """Try to extract an integer literal as a Lean SpecExpr."""
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        v = node.value
        if v < 0:
            return f".intLit ({v})"
        return f".intLit {v}"
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        if isinstance(node.operand, ast.Constant) and isinstance(node.operand.value, int):
            return f".intLit ({-node.operand.value})"
    return None


def _float_literal(node: ast.expr) -> Optional[str]:
    """Try to extract a float literal as a Lean SpecExpr."""
    if isinstance(node, ast.Constant) and isinstance(node.value, float):
        return f'.floatLit "{node.value}"'
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        if isinstance(node.operand, ast.Constant) and isinstance(node.operand.value, float):
            return f'.floatLit "{-node.operand.value}"'
    return None


def _numeric_literal(node: ast.expr) -> Optional[str]:
    """Try int first, then float."""
    r = _int_literal(node)
    if r:
        return r
    return _float_literal(node)


def _compare_to_spec_expr(node: ast.Compare, params: list[str]) -> str:
    """Handle comparison expressions."""
    # Single comparison: x >= N, x <= N, len(x) >= N, etc.
    if len(node.ops) == 1 and len(node.comparators) == 1:
        left = node.left
        op = node.ops[0]
        right = node.comparators[0]
        return _single_compare(left, op, right, params)

    # Chained comparison: N <= x <= M → intGe x N AND intLe x M
    # We can only represent this as placeholder for now
    # But try: 0 <= x <= 100 → two separate constraints
    if len(node.ops) == 2 and len(node.comparators) == 2:
        # a <= b <= c  or  a >= b >= c
        # Most common: N <= x <= M
        pass

    return ".placeholder"


def _single_compare(left: ast.expr, op: ast.cmpop, right: ast.expr,
                    params: list[str]) -> str:
    """Handle a single comparison like x >= N or len(x) <= N."""
    subj_left = _expr_to_subject(left)
    subj_right = _expr_to_subject(right)
    lit_left = _numeric_literal(left)
    lit_right = _numeric_literal(right)
    float_left = _float_literal(left)
    float_right = _float_literal(right)

    if isinstance(op, ast.GtE):
        # subject >= literal
        if subj_left and lit_right:
            if float_right and not _int_literal(right):
                return f".floatGe {subj_left} ({float_right})"
            return f".intGe {subj_left} ({lit_right})"
        # literal >= subject → subject <= literal
        if lit_left and subj_right:
            if float_left and not _int_literal(left):
                return f".floatLe {subj_right} ({float_left})"
            return f".intLe {subj_right} ({lit_left})"
        # subject >= subject
        if subj_left and subj_right:
            return f".intGe {subj_left} {subj_right}"

    if isinstance(op, ast.LtE):
        # subject <= literal
        if subj_left and lit_right:
            if float_right and not _int_literal(right):
                return f".floatLe {subj_left} ({float_right})"
            return f".intLe {subj_left} ({lit_right})"
        # literal <= subject → subject >= literal
        if lit_left and subj_right:
            if float_left and not _int_literal(left):
                return f".floatGe {subj_right} ({float_left})"
            return f".intGe {subj_right} ({lit_left})"
        # subject <= subject
        if subj_left and subj_right:
            return f".intLe {subj_left} {subj_right}"

    if isinstance(op, ast.Gt):
        # x > N → x >= N+1 for ints, or placeholder
        if subj_left and _int_literal(right):
            if isinstance(right, ast.Constant) and isinstance(right.value, int):
                return f".intGe {subj_left} (.intLit {right.value + 1})"
        # subject > subject → not (subject <= subject)
        if subj_left and subj_right:
            return f".intGe {subj_left} {subj_right}"

    if isinstance(op, ast.Lt):
        # x < N → x <= N-1 for ints
        if subj_left and _int_literal(right):
            if isinstance(right, ast.Constant) and isinstance(right.value, int):
                return f".intLe {subj_left} (.intLit {right.value - 1})"
        # subject < subject
        if subj_left and subj_right:
            return f".intLe {subj_left} {subj_right}"

    if isinstance(op, ast.Eq):
        # subject == subject → intEq
        if subj_left and subj_right:
            return f".intEq {subj_left} {subj_right}"
        if subj_left and lit_right:
            return f".intEq {subj_left} ({lit_right})"
        if lit_left and subj_right:
            return f".intEq ({lit_left}) {subj_right}"

    if isinstance(op, ast.NotEq):
        # x != 0 → .not (.intLe x 0 AND .intGe x 0) — can't express directly
        # But we can handle it for simple cases
        pass

    return ".placeholder"


def _try_enum_pattern(node: ast.BoolOp) -> Optional[str]:
    """Try to match x == "A" or x == "B" or ... → .enumMember"""
    if not isinstance(node.op, ast.Or):
        return None
    subject = None
    values = []
    for val in node.values:
        if not isinstance(val, ast.Compare):
            return None
        if len(val.ops) != 1 or not isinstance(val.ops[0], ast.Eq):
            return None
        if len(val.comparators) != 1:
            return None
        s = _expr_to_subject(val.left)
        if s is None:
            return None
        if subject is None:
            subject = s
        # Don't check subject equality (would need structural comparison)
        comp = val.comparators[0]
        if isinstance(comp, ast.Constant) and isinstance(comp.value, str):
            values.append(comp.value)
        else:
            return None
    if subject and values:
        vals_str = ", ".join(f'"{_escape_lean_str(v)}"' for v in values)
        return f".enumMember {subject} #[{vals_str}]"
    return None


def split_and_conditions(node: ast.expr) -> list[ast.expr]:
    """Split an 'and'-chained expression into individual conditions.
    Also splits chained comparisons like '0 <= x <= 100' into
    '0 <= x' and 'x <= 100'."""
    results = []
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        for val in node.values:
            results.extend(split_and_conditions(val))
    elif isinstance(node, ast.Compare) and len(node.ops) >= 2:
        # Chained comparison: a <= b <= c → (a <= b) and (b <= c)
        left = node.left
        for i, (op, comp) in enumerate(zip(node.ops, node.comparators)):
            single = ast.Compare(
                left=left, ops=[op], comparators=[comp],
                lineno=node.lineno, col_offset=node.col_offset,
                end_lineno=node.end_lineno, end_col_offset=node.end_col_offset
            )
            results.append(single)
            left = comp
    else:
        results.append(node)
    return results



# ---------------------------------------------------------------------------
# icontract decorator extraction
# ---------------------------------------------------------------------------

def get_decorator_kind(node: ast.expr) -> Optional[str]:
    """Classify an icontract decorator → 'require'|'ensure'|'snapshot'|'invariant'|None."""
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if isinstance(func, ast.Attribute):
        if isinstance(func.value, ast.Name) and func.value.id == "icontract":
            if func.attr in ("require", "ensure", "snapshot", "invariant"):
                return func.attr
    if isinstance(func, ast.Name):
        if func.id in ("require", "ensure", "snapshot", "invariant"):
            return func.id
    return None


def extract_lambda(node: ast.Call) -> Optional[ast.Lambda]:
    """Extract the lambda from an icontract decorator call."""
    if node.args and isinstance(node.args[0], ast.Lambda):
        return node.args[0]
    return None


def extract_description(node: ast.Call) -> Optional[str]:
    """Extract optional description string."""
    if len(node.args) >= 2 and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str):
        return node.args[1].value
    for kw in node.keywords:
        if kw.arg == "description" and isinstance(kw.value, ast.Constant):
            return kw.value.value
    return None


def extract_snapshot_name(node: ast.Call) -> Optional[str]:
    for kw in node.keywords:
        if kw.arg == "name" and isinstance(kw.value, ast.Constant):
            return kw.value.value
    return None


# ---------------------------------------------------------------------------
# Lean code generation
# ---------------------------------------------------------------------------

class LeanGenerator:
    """Generates Lean source code constructing Strata Signature values."""

    def __init__(self, module_name: str):
        self.module_name = module_name  # e.g., "bisect"
        self.lean_module = module_name.replace(".", "_")
        self.signatures: list[str] = []
        self.warnings: list[str] = []

    def process_file(self, tree: ast.Module):
        """Process a full Python module AST."""
        for node in tree.body:
            if isinstance(node, ast.FunctionDef):
                self._process_function(node, class_name=None)
            elif isinstance(node, ast.ClassDef):
                self._process_class(node)
            # Skip imports, assignments, etc.

    def _process_function(self, node: ast.FunctionDef,
                          class_name: Optional[str]) -> Optional[str]:
        """Process a function/method definition. Returns Lean FunctionDecl expression."""
        requires = []
        ensures = []
        snapshots = []
        remaining_decorators = []

        for dec in node.decorator_list:
            kind = get_decorator_kind(dec)
            if kind == "require":
                lam = extract_lambda(dec)
                desc = extract_description(dec)
                if lam:
                    params = [a.arg for a in lam.args.args]
                    # Split 'and' conditions and chained comparisons
                    parts = split_and_conditions(lam.body)
                    for part in parts:
                        spec_expr = expr_to_spec_expr(part, params)
                        source = ast.unparse(part)
                        requires.append((spec_expr, source, desc))
            elif kind == "ensure":
                lam = extract_lambda(dec)
                desc = extract_description(dec)
                if lam:
                    params = [a.arg for a in lam.args.args]
                    spec_expr = expr_to_spec_expr(lam.body, params)
                    source = ast.unparse(lam.body)
                    ensures.append((spec_expr, source, desc, params))
            elif kind == "snapshot":
                lam = extract_lambda(dec)
                name = extract_snapshot_name(dec) if isinstance(dec, ast.Call) else None
                if lam and name:
                    snapshots.append((ast.unparse(lam.body), name))
            elif kind == "invariant":
                self.warnings.append(f"  -- WARNING: @invariant on {node.name} not expressible")
            else:
                remaining_decorators.append(dec)

        # Build args
        args = self._build_args(node, class_name)

        # Return type
        ret_type = type_annotation_to_lean(node.returns, self.module_name)

        # Build preconditions (Assertion array)
        precond_strs = []
        for spec_expr, source, desc in requires:
            msg = desc if desc else source
            msg_escaped = _escape_lean_str(msg)
            precond_strs.append(
                f'    {{ message := #[.str "{msg_escaped}"],\n'
                f'      formula := {spec_expr} }}'
            )

        # Build postconditions (SpecExpr array)
        postcond_strs = []
        for spec_expr, source, desc, params in ensures:
            postcond_strs.append(f"    {spec_expr}")
            if spec_expr == ".placeholder":
                # Add the original source as a comment
                postcond_strs[-1] = f"    .placeholder /- {_escape_lean_comment(source)} -/"

        # Snapshot warnings
        snap_comments = []
        for snap_source, snap_name in snapshots:
            snap_comments.append(f"  -- snapshot: {snap_name} = {snap_source}")

        is_overload = any(
            isinstance(d, ast.Name) and d.id == "overload"
            for d in remaining_decorators
        )

        func_name = node.name

        precond_array = "#[]" if not precond_strs else (
            "#[\n" + ",\n".join(precond_strs) + "\n  ]"
        )
        postcond_array = "#[]" if not postcond_strs else (
            "#[\n" + ",\n".join(postcond_strs) + "\n  ]"
        )

        lines = []
        for c in snap_comments:
            lines.append(c)

        lines.append(f".functionDecl {{")
        lines.append(f'  loc := .none, nameLoc := .none, name := "{func_name}"')
        lines.append(f"  args := {args}")
        lines.append(f"  returnType := {ret_type}")
        lines.append(f"  isOverload := {str(is_overload).lower()}")
        lines.append(f"  preconditions := {precond_array}")
        lines.append(f"  postconditions := {postcond_array}")
        lines.append(f"}}")

        result = "\n".join(lines)

        if class_name is None:
            self.signatures.append(result)

        return result

    def _process_class(self, node: ast.ClassDef):
        """Process a class definition."""
        methods = []
        fields = []

        for item in node.body:
            if isinstance(item, ast.FunctionDef):
                if item.name == "__init__":
                    # Extract fields from __init__
                    fields.extend(self._extract_init_fields(item))
                else:
                    method_lean = self._process_function(item, class_name=node.name)
                    if method_lean:
                        methods.append(method_lean)
            elif isinstance(item, ast.AnnAssign):
                # Class-level annotated field
                if isinstance(item.target, ast.Name):
                    ft = type_annotation_to_lean(item.annotation, self.module_name)
                    fields.append(
                        f'{{ name := "{item.target.id}", type := {ft} }}'
                    )

        # Base classes
        bases = []
        for base in node.bases:
            if isinstance(base, ast.Name):
                bases.append(f'PythonIdent.mk "{self.module_name}" "{base.id}"')
            elif isinstance(base, ast.Attribute):
                bases.append(f'PythonIdent.mk "{ast.unparse(base.value)}" "{base.attr}"')

        bases_str = "#[]" if not bases else "#[" + ", ".join(bases) + "]"
        fields_str = "#[]" if not fields else "#[\n    " + ",\n    ".join(fields) + "\n  ]"
        methods_str = "#[]" if not methods else (
            "#[\n  " + ",\n  ".join(methods) + "\n  ]"
        )

        sig = (
            f'.classDef {{\n'
            f'  loc := .none, name := "{node.name}"\n'
            f'  bases := {bases_str}\n'
            f'  fields := {fields_str}\n'
            f'  methods := {methods_str}\n'
            f'}}'
        )
        self.signatures.append(sig)

    def _extract_init_fields(self, init_node: ast.FunctionDef) -> list[str]:
        """Extract self.x = ... assignments from __init__ as ClassField."""
        fields = []
        for stmt in init_node.body:
            if isinstance(stmt, ast.AnnAssign):
                if (isinstance(stmt.target, ast.Attribute) and
                    isinstance(stmt.target.value, ast.Name) and
                    stmt.target.value.id == "self"):
                    ft = type_annotation_to_lean(stmt.annotation, self.module_name)
                    fields.append(
                        f'{{ name := "{stmt.target.attr}", type := {ft} }}'
                    )
            elif isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if (isinstance(target, ast.Attribute) and
                        isinstance(target.value, ast.Name) and
                        target.value.id == "self"):
                        # No type annotation — use Any
                        fields.append(
                            f'{{ name := "{target.attr}", type := SpecType.ident .none .typingAny }}'
                        )
        return fields

    def _build_args(self, node: ast.FunctionDef, class_name: Optional[str]) -> str:
        """Build ArgDecls Lean expression from function arguments."""
        args_list = []
        for i, arg in enumerate(node.args.args):
            name = arg.arg
            if class_name and i == 0 and name == "self":
                # self parameter gets the class type
                tp = f'SpecType.pyClass .none "{class_name}" #[]'
            else:
                tp = type_annotation_to_lean(arg.annotation, self.module_name)

            # Check for default value
            defaults = node.args.defaults
            # defaults align to the end of args
            default_idx = i - (len(node.args.args) - len(defaults))
            if default_idx >= 0 and default_idx < len(defaults):
                default_node = defaults[default_idx]
                if isinstance(default_node, ast.Constant) and default_node.value is None:
                    args_list.append(f'{{ name := "{name}", type := {tp}, default := some .none }}')
                else:
                    # Other defaults — use .none as approximation
                    args_list.append(f'{{ name := "{name}", type := {tp}, default := some .none }}')
            else:
                args_list.append(f'{{ name := "{name}", type := {tp} }}')

        kwonly_list = []
        for i, arg in enumerate(node.args.kwonlyargs):
            name = arg.arg
            tp = type_annotation_to_lean(arg.annotation, self.module_name)
            if i < len(node.args.kw_defaults) and node.args.kw_defaults[i] is not None:
                kwonly_list.append(f'{{ name := "{name}", type := {tp}, default := some .none }}')
            else:
                kwonly_list.append(f'{{ name := "{name}", type := {tp} }}')

        args_str = "#[]" if not args_list else "#[\n      " + ",\n      ".join(args_list) + "\n    ]"
        kwonly_str = "#[]" if not kwonly_list else "#[\n      " + ",\n      ".join(kwonly_list) + "\n    ]"

        return f"{{ args := {args_str}, kwonly := {kwonly_str} }}"

    def generate_lean(self) -> str:
        """Generate the complete Lean source file."""
        lines = [
            f"/-",
            f"  Auto-generated from icontract specs: {self.module_name}",
            f"  Source: CPython-icontract/contracts/{self.module_name}.py",
            f"-/",
            f"import Strata.Languages.Python.Specs.Decls",
            f"",
            f"namespace Strata.Python.Specs.IContract.{self.lean_module.capitalize()}",
            f"",
            f"open Strata.Python.Specs",
            f"open Strata.Python",
            f"",
            f"def signatures : Array Signature := #[",
        ]

        for i, sig in enumerate(self.signatures):
            # Indent each signature
            indented = "  " + sig.replace("\n", "\n  ")
            if i < len(self.signatures) - 1:
                indented += ","
            lines.append(indented)

        lines.append("]")
        lines.append("")

        if self.warnings:
            lines.append("/-")
            lines.append("Conversion warnings:")
            for w in self.warnings:
                lines.append(w)
            lines.append("-/")
            lines.append("")

        lines.append(f"end Strata.Python.Specs.IContract.{self.lean_module.capitalize()}")
        lines.append("")

        return "\n".join(lines)


def _escape_lean_comment(s: str) -> str:
    """Escape a string for use inside a Lean block comment."""
    return s.replace("-/", "- /").replace("/-", "/ -")



# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def convert_file(input_path: Path, output_path: Path, module_name: Optional[str] = None):
    """Convert a single icontract Python file to Lean."""
    source = input_path.read_text()
    tree = ast.parse(source, filename=str(input_path))

    if module_name is None:
        module_name = input_path.stem

    gen = LeanGenerator(module_name)
    gen.process_file(tree)
    lean_source = gen.generate_lean()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(lean_source)
    print(f"  {input_path} → {output_path} ({len(gen.signatures)} signatures)")
    if gen.warnings:
        for w in gen.warnings:
            print(f"    {w}")


def convert_directory(input_dir: Path, output_dir: Path):
    """Convert all .py files in a directory."""
    py_files = sorted(input_dir.glob("*.py"))
    # Also handle subdirectories
    for subdir in sorted(input_dir.iterdir()):
        if subdir.is_dir() and not subdir.name.startswith((".", "__")):
            py_files.extend(sorted(subdir.glob("*.py")))

    count = 0
    for py_file in py_files:
        if py_file.name == "__init__.py":
            continue
        # Determine module name from path relative to input_dir
        rel = py_file.relative_to(input_dir)
        parts = list(rel.parts)
        parts[-1] = rel.stem  # remove .py
        module_name = ".".join(parts)

        # Output path mirrors structure
        out_file = output_dir / rel.with_suffix(".lean")
        try:
            convert_file(py_file, out_file, module_name)
            count += 1
        except SyntaxError as e:
            print(f"  SKIP {py_file}: {e}")
        except Exception as e:
            print(f"  ERROR {py_file}: {e}")

    print(f"\nConverted {count} files.")


def convert_file_ion(input_path: Path, output_path: Path, module_name: Optional[str] = None,
                     only_decorated: bool = False):
    """Convert a single icontract Python file to .pyspec.st.ion."""
    from strata.icontract_ion import IonSpecGenerator

    source = input_path.read_text()
    tree = ast.parse(source, filename=str(input_path))

    if module_name is None:
        module_name = input_path.stem

    gen = IonSpecGenerator(module_name)
    gen.process_file(tree, only_decorated=only_decorated)
    count = gen.write_ion(output_path)
    print(f"  {input_path} → {output_path} ({count} signatures)")
    if gen.warnings:
        for w in gen.warnings:
            print(f"    {w}")


def convert_directory_ion(input_dir: Path, output_dir: Path):
    """Convert all .py files in a directory to .pyspec.st.ion."""
    py_files = sorted(input_dir.glob("*.py"))
    for subdir in sorted(input_dir.iterdir()):
        if subdir.is_dir() and not subdir.name.startswith((".", "__")):
            py_files.extend(sorted(subdir.glob("*.py")))

    count = 0
    for py_file in py_files:
        if py_file.name == "__init__.py":
            continue
        rel = py_file.relative_to(input_dir)
        parts = list(rel.parts)
        parts[-1] = rel.stem
        module_name = ".".join(parts)
        out_file = output_dir / rel.with_suffix(".pyspec.st.ion")
        try:
            convert_file_ion(py_file, out_file, module_name)
            count += 1
        except SyntaxError as e:
            print(f"  SKIP {py_file}: {e}")
        except Exception as e:
            print(f"  ERROR {py_file}: {e}")

    print(f"\nConverted {count} files.")


def main():
    parser = argparse.ArgumentParser(
        description="Convert icontract Python specs to Strata Signature values"
    )
    parser.add_argument("input", help="Input .py file or directory")
    parser.add_argument("output", help="Output file or directory")
    parser.add_argument("--module", help="Override module name", default=None)
    parser.add_argument("--format", choices=["lean", "ion"], default="ion",
                        help="Output format: 'ion' (default) for .pyspec.st.ion, 'lean' for .lean")
    parser.add_argument("--only-decorated", action="store_true",
                        help="Only emit specs for functions with icontract decorators")
    args = parser.parse_args()

    input_path = Path(args.input)
    output_path = Path(args.output)

    if args.format == "ion":
        if input_path.is_file():
            if not output_path.suffix == ".ion":
                output_path = output_path / (input_path.stem + ".pyspec.st.ion")
            convert_file_ion(input_path, output_path, args.module,
                             only_decorated=args.only_decorated)
        elif input_path.is_dir():
            convert_directory_ion(input_path, output_path)
        else:
            print(f"Error: {input_path} not found", file=sys.stderr)
            sys.exit(1)
    else:
        if input_path.is_file():
            if output_path.suffix != ".lean":
                output_path = output_path / (input_path.stem + ".lean")
            convert_file(input_path, output_path, args.module)
        elif input_path.is_dir():
            convert_directory(input_path, output_path)
        else:
            print(f"Error: {input_path} not found", file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
