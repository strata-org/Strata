"""
Bridge between icontract AST processing and Ion DDM output.

Uses the existing expr_to_spec_expr / type_annotation_to_lean logic
but outputs Ion binary instead of Lean text.
"""

import ast
from pathlib import Path
from typing import Optional

from strata.icontract import (
    get_decorator_kind, extract_lambda, extract_description,
    extract_snapshot_name, expr_to_spec_expr, split_and_conditions,
    type_annotation_to_lean, BUILTIN_TYPE_MAP, TYPING_MAP,
)
from strata.ddm_writer import IonDDMWriter


# Map from Lean SpecType text to DDM Ion ident strings
_BUILTIN_IDENT_MAP = {
    ".builtinsInt": "builtins.int",
    ".builtinsFloat": "builtins.float",
    ".builtinsStr": "builtins.str",
    ".builtinsBool": "builtins.bool",
    ".builtinsBytes": "builtins.bytes",
    ".builtinsBytearray": "builtins.bytearray",
    ".builtinsComplex": "builtins.complex",
    ".builtinsDict": "builtins.dict",
    ".typingList": "typing.List",
    ".typingDict": "typing.Dict",
    ".typingSequence": "typing.Sequence",
    ".typingMapping": "typing.Mapping",
    ".typingAny": "typing.Any",
    ".typingUnion": "typing.Union",
    ".typingLiteral": "typing.Literal",
    ".typingGenerator": "typing.Generator",
}


class IonSpecGenerator:
    """Generates .pyspec.st.ion files from icontract-decorated Python."""

    def __init__(self, module_name: str):
        self.module_name = module_name
        self.command_fns = []
        self.warnings = []

    def _has_icontract_decorator(self, node: ast.FunctionDef) -> bool:
        """Check if a function has any icontract decorators."""
        return any(get_decorator_kind(dec) is not None for dec in node.decorator_list)

    def process_file(self, tree: ast.Module, only_decorated: bool = False):
        for node in tree.body:
            if isinstance(node, ast.FunctionDef):
                if only_decorated and not self._has_icontract_decorator(node):
                    continue
                self._process_function(node, class_name=None)
            elif isinstance(node, ast.ClassDef):
                self._process_class(node)

    def _emit_type(self, w: IonDDMWriter, node: Optional[ast.expr]):
        """Emit a SpecType Ion node from a Python type annotation."""
        if node is None:
            w._typeIdentNoArgs("typing.Any")
            return

        if isinstance(node, ast.Constant):
            if node.value is None:
                w._typeIdentNoArgs("_types.NoneType")
                return
            w._typeIdentNoArgs("typing.Any")
            return

        if isinstance(node, ast.Name):
            name = node.id
            if name == "None" or name == "NoneType":
                w._typeIdentNoArgs("_types.NoneType")
                return
            if name in BUILTIN_TYPE_MAP:
                w._typeIdentNoArgs(_BUILTIN_IDENT_MAP[BUILTIN_TYPE_MAP[name]])
                return
            if name in TYPING_MAP:
                w._typeIdentNoArgs(_BUILTIN_IDENT_MAP[TYPING_MAP[name]])
                return
            # User-defined class
            w._op("PythonSpecs.typeClassNoArgs", lambda: w._ident(name))
            return

        if isinstance(node, ast.Subscript):
            base = node.value
            base_name = ""
            if isinstance(base, ast.Name):
                base_name = base.id

            if base_name in ("List", "Sequence"):
                ident = _BUILTIN_IDENT_MAP[TYPING_MAP[base_name]]
                w._typeIdent(ident,
                    lambda: w._commaSepList(
                        lambda: self._emit_type(w, node.slice)))
                return

            if base_name in ("Dict", "Mapping"):
                ident = _BUILTIN_IDENT_MAP[TYPING_MAP[base_name]]
                if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 2:
                    w._typeIdent(ident,
                        lambda: w._commaSepList(
                            lambda: self._emit_type(w, node.slice.elts[0]),
                            lambda: self._emit_type(w, node.slice.elts[1])))
                else:
                    w._typeIdentNoArgs(ident)
                return

            if base_name == "Optional":
                # Optional[T] → union of T and None
                # For simplicity, just emit the inner type
                self._emit_type(w, node.slice)
                return

        # Fallback
        w._typeIdentNoArgs("typing.Any")

    def _emit_spec_expr(self, w: IonDDMWriter, lean_expr: str):
        """Convert a Lean SpecExpr string to Ion DDM nodes.

        This parses the string output of expr_to_spec_expr and emits
        the corresponding Ion DDM nodes.
        """
        # Parse the Lean-style SpecExpr string into Ion DDM calls
        self._emit_spec_expr_parsed(w, lean_expr)

    def _emit_spec_expr_parsed(self, w: IonDDMWriter, expr: str):
        """Recursively emit Ion for a Lean SpecExpr string."""
        expr = expr.strip()

        if expr == ".placeholder":
            w._placeholderExpr()
            return

        if expr.startswith('.var "') and expr.endswith('"'):
            name = expr[6:-1]
            w._varExpr(name)
            return

        if expr.startswith('.isInstanceOf '):
            # .isInstanceOf (.var "x") "Type"
            rest = expr[len('.isInstanceOf '):]
            subj_end = self._find_matching_paren(rest, 0)
            subj = rest[1:subj_end]  # strip outer parens
            type_name = rest[subj_end+2:].strip().strip('"')
            w._isInstanceOfExpr(
                lambda s=subj: self._emit_spec_expr_parsed(w, s),
                type_name)
            return

        if expr.startswith('.len '):
            rest = expr[len('.len '):]
            inner = rest.strip('()')
            w._lenExpr(lambda i=inner: self._emit_spec_expr_parsed(w, i))
            return

        if expr.startswith('.intLit '):
            val_str = expr[len('.intLit '):]
            val_str = val_str.strip('()')
            w._intExpr(int(val_str))
            return

        if expr.startswith('.intGe '):
            rest = expr[len('.intGe '):]
            subj, bound = self._split_two_args(rest)
            w._intGeExpr(
                lambda s=subj: self._emit_spec_expr_parsed(w, s),
                lambda b=bound: self._emit_spec_expr_parsed(w, b))
            return

        if expr.startswith('.intLe '):
            rest = expr[len('.intLe '):]
            subj, bound = self._split_two_args(rest)
            w._intLeExpr(
                lambda s=subj: self._emit_spec_expr_parsed(w, s),
                lambda b=bound: self._emit_spec_expr_parsed(w, b))
            return

        if expr.startswith('.intAdd '):
            rest = expr[len('.intAdd '):]
            left, right = self._split_two_args(rest)
            w._intAddExpr(
                lambda l=left: self._emit_spec_expr_parsed(w, l),
                lambda r=right: self._emit_spec_expr_parsed(w, r))
            return

        if expr.startswith('.intSub '):
            rest = expr[len('.intSub '):]
            left, right = self._split_two_args(rest)
            w._intSubExpr(
                lambda l=left: self._emit_spec_expr_parsed(w, l),
                lambda r=right: self._emit_spec_expr_parsed(w, r))
            return

        if expr.startswith('.intMul '):
            rest = expr[len('.intMul '):]
            left, right = self._split_two_args(rest)
            w._intMulExpr(
                lambda l=left: self._emit_spec_expr_parsed(w, l),
                lambda r=right: self._emit_spec_expr_parsed(w, r))
            return

        if expr.startswith('.intEq '):
            rest = expr[len('.intEq '):]
            left, right = self._split_two_args(rest)
            w._intEqExpr(
                lambda l=left: self._emit_spec_expr_parsed(w, l),
                lambda r=right: self._emit_spec_expr_parsed(w, r))
            return

        if expr.startswith('.floatLit "') and expr.endswith('"'):
            val = expr[len('.floatLit "'):-1]
            w._floatExpr(val)
            return

        if expr.startswith('.floatGe '):
            rest = expr[len('.floatGe '):]
            subj, bound = self._split_two_args(rest)
            w._floatGeExpr(
                lambda s=subj: self._emit_spec_expr_parsed(w, s),
                lambda b=bound: self._emit_spec_expr_parsed(w, b))
            return

        if expr.startswith('.floatLe '):
            rest = expr[len('.floatLe '):]
            subj, bound = self._split_two_args(rest)
            w._floatLeExpr(
                lambda s=subj: self._emit_spec_expr_parsed(w, s),
                lambda b=bound: self._emit_spec_expr_parsed(w, b))
            return

        if expr.startswith('.not '):
            inner = expr[len('.not '):].strip('()')
            w._notExpr(lambda i=inner: self._emit_spec_expr_parsed(w, i))
            return

        if expr.startswith('.getIndex '):
            rest = expr[len('.getIndex '):]
            subj_end = self._find_matching_paren(rest, 0)
            subj = rest[1:subj_end]
            field = rest[subj_end+2:].strip().strip('"')
            w._getIndexExpr(
                lambda s=subj: self._emit_spec_expr_parsed(w, s),
                field)
            return

        if expr.startswith('.forallList '):
            rest = expr[len('.forallList '):]
            list_end = self._find_matching_paren(rest, 0)
            list_expr = rest[1:list_end]
            remaining = rest[list_end+2:].strip()
            # Parse "varName" (body)
            var_end = remaining.index('"', 1)
            var_name = remaining[1:var_end]
            body = remaining[var_end+2:].strip().strip('()')
            w._forallListExpr(
                lambda l=list_expr: self._emit_spec_expr_parsed(w, l),
                var_name,
                lambda b=body: self._emit_spec_expr_parsed(w, b))
            return

        # Fallback: placeholder
        w._placeholderExpr()

    def _find_matching_paren(self, s: str, start: int) -> int:
        """Find the index of the closing paren matching s[start]='('."""
        depth = 0
        for i in range(start, len(s)):
            if s[i] == '(':
                depth += 1
            elif s[i] == ')':
                depth -= 1
                if depth == 0:
                    return i
        return len(s) - 1

    def _split_two_args(self, rest: str) -> tuple:
        """Split 'arg1 arg2' where args may be parenthesized."""
        rest = rest.strip()
        if rest.startswith('('):
            end = self._find_matching_paren(rest, 0)
            first = rest[1:end]
            second = rest[end+2:].strip().strip('()')
        else:
            # Simple: .var "x" or similar — find first space after first token
            parts = rest.split(' ', 1)
            if len(parts) == 2 and parts[0].startswith('.'):
                # e.g., '.var "x"' — need to be smarter
                # Find the boundary between two top-level expressions
                first, second = self._split_top_level(rest)
            else:
                first = parts[0].strip('()')
                second = parts[1].strip('()') if len(parts) > 1 else '.placeholder'
        return first, second

    def _split_top_level(self, s: str) -> tuple:
        """Split a string into two top-level s-expressions."""
        s = s.strip()
        depth = 0
        i = 0
        while i < len(s):
            if s[i] == '(':
                depth += 1
            elif s[i] == ')':
                depth -= 1
            elif s[i] == ' ' and depth == 0:
                # Check if we've consumed a complete expression
                left = s[:i].strip()
                right = s[i+1:].strip()
                # A complete expression either starts with ( or with .something "..."
                if left and (left.startswith('(') or not right.startswith('"')):
                    if self._is_complete_expr(left):
                        return left.strip('()'), right.strip('()')
            i += 1
        return s.strip('()'), '.placeholder'

    def _is_complete_expr(self, s: str) -> bool:
        """Check if s looks like a complete SpecExpr."""
        s = s.strip()
        if s.startswith('(') and s.endswith(')'):
            return True
        if s.startswith('.') and '"' in s:
            return True
        return False

    def _process_function(self, node: ast.FunctionDef, class_name=None):
        requires = []
        ensures = []
        remaining_decorators = []

        for dec in node.decorator_list:
            kind = get_decorator_kind(dec)
            if kind == "require":
                lam = extract_lambda(dec)
                desc = extract_description(dec)
                if lam:
                    params = [a.arg for a in lam.args.args]
                    parts = split_and_conditions(lam.body)
                    for part in parts:
                        spec_expr = expr_to_spec_expr(part, params)
                        source = ast.unparse(part)
                        msg = desc if desc else source
                        requires.append((spec_expr, msg))
            elif kind == "ensure":
                lam = extract_lambda(dec)
                if lam:
                    params = [a.arg for a in lam.args.args]
                    spec_expr = expr_to_spec_expr(lam.body, params)
                    ensures.append(spec_expr)
            else:
                remaining_decorators.append(dec)

        is_overload = any(
            isinstance(d, ast.Name) and d.id == "overload"
            for d in remaining_decorators
        )

        func_name = node.name
        func_node = node
        class_nm = class_name

        def make_command(w: IonDDMWriter):
            # Build arg fns
            arg_fns = []
            for i, arg in enumerate(func_node.args.args):
                a_name = arg.arg
                a_ann = arg.annotation
                a_idx = i
                defaults = func_node.args.defaults
                default_idx = a_idx - (len(func_node.args.args) - len(defaults))
                has_default = 0 <= default_idx < len(defaults)

                if class_nm and a_idx == 0 and a_name == "self":
                    def make_type_fn(w2, cn=class_nm):
                        w2._op("PythonSpecs.typeClassNoArgs", lambda: w2._ident(cn))
                    arg_fns.append(lambda n=a_name, hd=has_default, cn=class_nm:
                        w._mkArgDecl(n, lambda: make_type_fn(w, cn), hd))
                else:
                    def make_type_fn2(w2, ann=a_ann):
                        self._emit_type(w2, ann)
                    arg_fns.append(lambda n=a_name, hd=has_default, ann=a_ann:
                        w._mkArgDecl(n, lambda: self._emit_type(w, ann), hd))

            kwonly_fns = []
            for i, arg in enumerate(func_node.args.kwonlyargs):
                a_name = arg.arg
                a_ann = arg.annotation
                has_default = (i < len(func_node.args.kw_defaults)
                               and func_node.args.kw_defaults[i] is not None)
                kwonly_fns.append(lambda n=a_name, hd=has_default, ann=a_ann:
                    w._mkArgDecl(n, lambda: self._emit_type(w, ann), hd))

            # Return type
            ret_ann = func_node.returns

            # Preconditions
            precond_fns = []
            for spec_expr, msg in requires:
                precond_fns.append(lambda se=spec_expr, m=msg:
                    w._mkAssertion(
                        lambda: self._emit_spec_expr_parsed(w, se),
                        m))

            # Postconditions
            postcond_fns = []
            for se in ensures:
                postcond_fns.append(lambda s=se:
                    w._op("PythonSpecs.mkPostconditionEntry",
                           lambda: self._emit_spec_expr_parsed(w, s)))

            w._functionDecl(lambda: w._mkFunDecl(
                func_name, arg_fns, kwonly_fns,
                lambda: self._emit_type(w, ret_ann),
                is_overload, precond_fns, postcond_fns))

        if class_name is None:
            self.command_fns.append(make_command)

        return make_command

    def _process_class(self, node: ast.ClassDef):
        method_fns = []
        for item in node.body:
            if isinstance(item, ast.FunctionDef):
                if item.name != "__init__":
                    fn = self._process_function(item, class_name=node.name)
                    if fn:
                        method_fns.append(fn)

        cls_name = node.name
        mfns = method_fns

        def make_class_command(w: IonDDMWriter):
            w._classDef(lambda: w._op("PythonSpecs.mkClassDecl",
                lambda: w._strlit(cls_name),
                lambda: w._seq(),  # bases
                lambda: w._seq(),  # fields
                lambda: w._seq(),  # classVars
                lambda: w._seq(),  # subclasses
                lambda: w._seq(*[lambda f=f: f(w) for f in mfns]),
                lambda: w._op("Init.boolFalse"),  # exhaustive
            ))

        self.command_fns.append(make_class_command)

    def write_ion(self, output_path: Path):
        """Write the .pyspec.st.ion file."""
        w = IonDDMWriter()
        w.write_program([lambda f=f: f(w) for f in self.command_fns])
        data = w.get_bytes()
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(data)
        return len(self.command_fns)
