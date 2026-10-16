# Quick Start: Build a Strata Front-End

This tutorial walks you through building a minimal front-end for a toy language called Calc. By the end, you'll have a working pipeline that parses Calc source code, translates it to the Laurel dialect, and verifies contracts using Strata's SMT-based verification.

The full pipeline: **Calc source → Python parser → Calc AST → Lean translator → Laurel → Core → SMT → verification results**.

## What we're building

Calc is a tiny imperative language with integer arithmetic, `if/else`, and functions with `requires`/`ensures` contracts:

```
function abs(x: int) returns (result: int)
  requires true
  ensures result >= 0
{
  if (x < 0) {
    result := 0 - x
  } else {
    result := x
  }
}
```

This is enough to exercise the full Strata verification pipeline: parsing, dialect definition, translation to Laurel, and SMT-based contract checking.

## Prerequisites

- Lean 4 (see `lean-toolchain` in the Strata repo)
- Python 3.12+
- cvc5 on your `PATH` (for SMT solving)
- A clone of [strata-org/Strata](https://github.com/strata-org/Strata)

## Step 1: Define the Calc dialect

We define a DDM dialect for Calc in Python using `strata.base`. This generates the AST data structures and serialization code automatically.

Create `Tools/Calc/calc_dialect.py`:

```python
"""Calc dialect definition and parser."""
import sys
from pathlib import Path

# Add Strata's Python tools to the path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "Python"))

from strata.base import (
    Dialect, ArgDecl, SynCatDecl, SyntaxCat,
    Init, NumLit, StrLit, Ident, Seq, OptionArg, SourceRange,
    Operation, Program
)

def gen_dialect() -> Dialect:
    """Define the Calc dialect."""
    Calc = Dialect("Calc")
    Calc.add_import("Init")

    # Types (just int and bool for now)
    Calc.add_syncat("CalcType")
    Calc.add_op("IntType", Calc.CalcType())
    Calc.add_op("BoolType", Calc.CalcType())

    # Expressions
    Calc.add_syncat("Expr")
    Calc.add_op("IntLit", ArgDecl("value", Init.Num()), Calc.Expr())
    Calc.add_op("BoolLit", ArgDecl("value", Init.Num()), Calc.Expr())  # 0=false, 1=true
    Calc.add_op("Var", ArgDecl("name", Init.Str()), Calc.Expr())
    Calc.add_op("BinOp",
        ArgDecl("op", Init.Str()),    # "+", "-", "*", "<", ">=", "==", "&&", "||"
        ArgDecl("lhs", Calc.Expr()),
        ArgDecl("rhs", Calc.Expr()),
        Calc.Expr())
    Calc.add_op("UnaryOp",
        ArgDecl("op", Init.Str()),     # "-", "!"
        ArgDecl("operand", Calc.Expr()),
        Calc.Expr())

    # Statements
    Calc.add_syncat("Stmt")
    Calc.add_op("Assign",
        ArgDecl("target", Init.Str()),
        ArgDecl("value", Calc.Expr()),
        Calc.Stmt())
    Calc.add_op("IfElse",
        ArgDecl("cond", Calc.Expr()),
        ArgDecl("thenBranch", Calc.Stmt()),
        ArgDecl("elseBranch", Init.Option(Calc.Stmt())),
        Calc.Stmt())
    Calc.add_op("Block",
        ArgDecl("stmts", Init.Seq(Calc.Stmt())),
        Calc.Stmt())
    Calc.add_op("Return",
        ArgDecl("value", Calc.Expr()),
        Calc.Stmt())

    # Contracts
    Calc.add_syncat("Contract")
    Calc.add_op("Requires", ArgDecl("cond", Calc.Expr()), Calc.Contract())
    Calc.add_op("Ensures", ArgDecl("cond", Calc.Expr()), Calc.Contract())

    # Parameters
    Calc.add_syncat("Param")
    Calc.add_op("Param",
        ArgDecl("name", Init.Str()),
        ArgDecl("type", Calc.CalcType()),
        Calc.Param())

    # Functions (top-level)
    Calc.add_op("Function",
        ArgDecl("name", Init.Str()),
        ArgDecl("params", Init.Seq(Calc.Param())),
        ArgDecl("returns", Init.Seq(Calc.Param())),
        ArgDecl("contracts", Init.Seq(Calc.Contract())),
        ArgDecl("body", Calc.Stmt()),
        Init.Command())

    return Calc
```

## Step 2: Build the parser

We write a simple recursive-descent parser in Python. It parses Calc source text and emits DDM `Operation` nodes using the dialect we just defined.

Add to `Tools/Calc/calc_dialect.py`:

```python
import re

class CalcParser:
    """Recursive-descent parser for Calc."""

    def __init__(self, dialect: Dialect):
        self.d = dialect
        self.tokens: list[str] = []
        self.pos = 0

    def tokenize(self, source: str) -> list[str]:
        pattern = r'>=|<=|==|!=|&&|\|\||[a-zA-Z_]\w*|\d+|[{}();:,+\-*/<>=!]'
        return re.findall(pattern, source)

    def peek(self) -> str:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else ""

    def advance(self) -> str:
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect(self, tok: str):
        got = self.advance()
        assert got == tok, f"Expected '{tok}', got '{got}'"

    def parse_type(self) -> Operation:
        tok = self.advance()
        if tok == "int":
            return self.d.IntType()
        elif tok == "bool":
            return self.d.BoolType()
        raise ValueError(f"Unknown type: {tok}")

    def parse_param(self) -> Operation:
        name = self.advance()
        self.expect(":")
        ty = self.parse_type()
        return self.d.Param(StrLit(name), ty)

    def parse_param_list(self) -> list[Operation]:
        self.expect("(")
        params = []
        while self.peek() != ")":
            if params:
                self.expect(",")
            params.append(self.parse_param())
        self.expect(")")
        return params

    def parse_atom(self) -> Operation:
        tok = self.peek()
        if tok == "(":
            self.advance()
            expr = self.parse_expr()
            self.expect(")")
            return expr
        if tok == "!":
            self.advance()
            operand = self.parse_atom()
            return self.d.UnaryOp(StrLit("!"), operand)
        if tok == "true":
            self.advance()
            return self.d.BoolLit(NumLit(1))
        if tok == "false":
            self.advance()
            return self.d.BoolLit(NumLit(0))
        if tok.isdigit():
            self.advance()
            return self.d.IntLit(NumLit(int(tok)))
        if tok == "-" and (self.pos == 0 or self.tokens[self.pos - 1] in ("(", ",", ":=")):
            self.advance()
            operand = self.parse_atom()
            return self.d.UnaryOp(StrLit("-"), operand)
        # identifier
        self.advance()
        return self.d.Var(StrLit(tok))

    def parse_expr(self, min_prec: int = 0) -> Operation:
        """Pratt parser for expressions."""
        lhs = self.parse_atom()
        prec_map = {
            "||": 1, "&&": 2,
            "==": 3, "!=": 3, "<": 3, "<=": 3, ">": 3, ">=": 3,
            "+": 4, "-": 4,
            "*": 5,
        }
        while self.peek() in prec_map and prec_map[self.peek()] >= min_prec:
            op = self.advance()
            rhs = self.parse_expr(prec_map[op] + 1)
            lhs = self.d.BinOp(StrLit(op), lhs, rhs)
        return lhs

    def parse_stmt(self) -> Operation:
        tok = self.peek()
        if tok == "{":
            return self.parse_block()
        if tok == "if":
            return self.parse_if()
        if tok == "return":
            self.advance()
            value = self.parse_expr()
            return self.d.Return(value)
        # assignment: name := expr
        name = self.advance()
        self.expect(":=")
        value = self.parse_expr()
        return self.d.Assign(StrLit(name), value)

    def parse_block(self) -> Operation:
        self.expect("{")
        stmts = []
        while self.peek() != "}":
            stmts.append(self.parse_stmt())
            if self.peek() == ";":
                self.advance()
        self.expect("}")
        return self.d.Block(Seq(tuple(stmts)))

    def parse_if(self) -> Operation:
        self.expect("if")
        self.expect("(")
        cond = self.parse_expr()
        self.expect(")")
        then_branch = self.parse_block()
        else_branch = None
        if self.peek() == "else":
            self.advance()
            else_branch = self.parse_block()
        return self.d.IfElse(cond, then_branch, OptionArg(else_branch))

    def parse_contracts(self) -> list[Operation]:
        contracts = []
        while self.peek() in ("requires", "ensures"):
            kind = self.advance()
            cond = self.parse_expr()
            if kind == "requires":
                contracts.append(self.d.Requires(cond))
            else:
                contracts.append(self.d.Ensures(cond))
        return contracts

    def parse_function(self) -> Operation:
        self.expect("function")
        name = self.advance()
        params = self.parse_param_list()
        self.expect("returns")
        returns = self.parse_param_list()
        contracts = self.parse_contracts()
        body = self.parse_block()
        return self.d.Function(
            StrLit(name),
            Seq(tuple(params)),
            Seq(tuple(returns)),
            Seq(tuple(contracts)),
            body,
        )

    def parse_program(self, source: str) -> Program:
        self.tokens = self.tokenize(source)
        self.pos = 0
        prog = Program(self.d)
        while self.pos < len(self.tokens):
            prog.add(self.parse_function())
        return prog
```

## Step 3: Serialize to Ion

Now we can parse a Calc program and serialize it to the Ion binary format that Strata reads on the Lean side.

Add to `Tools/Calc/calc_dialect.py`:

```python
def main():
    import sys
    dialect = gen_dialect()

    # Save the dialect definition (needed by Lean's #load_dialect)
    dialect_dir = Path(__file__).resolve().parent / "dialects"
    dialect_dir.mkdir(exist_ok=True)
    dialect.write(dialect_dir / "Calc.dialect.st.ion")

    # Parse and serialize a Calc source file
    if len(sys.argv) < 2:
        print("Usage: python calc_dialect.py <file.calc>")
        sys.exit(1)

    source = Path(sys.argv[1]).read_text()
    parser = CalcParser(dialect)
    program = parser.parse_program(source)
    output = Path(sys.argv[1]).with_suffix(".calc.ion")
    program.write(output)
    print(f"Wrote {output}")

if __name__ == "__main__":
    main()
```

Test it with a sample program. Create `Examples/Abs.calc`:

```
function abs(x: int) returns (result: int)
  requires true
  ensures result >= 0
{
  if (x < 0) {
    result := 0 - x
  } else {
    result := x
  }
}
```

Run:

```bash
python Tools/Calc/calc_dialect.py Examples/Abs.calc
# Writes Examples/Abs.calc.ion
```

## Step 4: Write the Lean-side translator (Calc → Laurel)

On the Lean side, we load the Calc dialect, deserialize the Ion file, and translate each Calc AST node into Laurel's `StmtExprMd` / `Procedure` / `Program` types. Then we call `Laurel.verifyToVcResults` which handles the entire Laurel → Core → SMT pipeline.

Create `Strata/Languages/Calc/Calc.lean`:

```lean
/-
  Calc → Laurel translator.
  Translates the Calc toy language into Laurel, then verifies using the
  Laurel → Core → SMT pipeline.
-/
module

import Strata.DDM.Integration.Lean
import Strata.DDM.Ion
import Strata.DDM.AST
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Core.Verifier

open Strata Laurel

namespace Strata.Calc

-- Load the Calc dialect definition generated by the Python script
#load_dialect "../../../Tools/Calc/dialects/Calc.dialect.st.ion"
#strata_gen Calc

/-! ## Helper: wrap a value with empty metadata -/

private def md : Imperative.MetaData Core.Expression := .empty

private def wm (v : α) : WithMetadata α := ⟨v, md⟩

/-! ## Translate Calc types to Laurel types -/

def translateType : Calc.CalcType SourceRange → HighTypeMd
  | .IntType _ => wm .TInt
  | .BoolType _ => wm .TBool

/-! ## Translate Calc expressions to Laurel StmtExprMd -/

def translateExpr : Calc.Expr SourceRange → StmtExprMd
  | .IntLit _ n => wm (.LiteralInt n)
  | .BoolLit _ n => wm (.LiteralBool (n != 0))
  | .Var _ name => wm (.Identifier (mkId name))
  | .UnaryOp _ op operand =>
    let operand' := translateExpr operand
    match op with
    | "-" => wm (.PrimitiveOp .Neg [operand'])
    | "!" => wm (.PrimitiveOp .Not [operand'])
    | _ => wm (.Hole)  -- unsupported
  | .BinOp _ op lhs rhs =>
    let lhs' := translateExpr lhs
    let rhs' := translateExpr rhs
    let laurelOp := match op with
      | "+"  => Operation.Add
      | "-"  => Operation.Sub
      | "*"  => Operation.Mul
      | "<"  => Operation.Lt
      | "<=" => Operation.Leq
      | ">"  => Operation.Gt
      | ">=" => Operation.Geq
      | "==" => Operation.Eq
      | "!=" => Operation.Neq
      | "&&" => Operation.And
      | "||" => Operation.Or
      | _    => Operation.Eq  -- fallback
    wm (.PrimitiveOp laurelOp [lhs', rhs'])

/-! ## Translate Calc statements to Laurel StmtExprMd -/

def translateStmt : Calc.Stmt SourceRange → StmtExprMd
  | .Assign _ target value =>
    let target' := wm (StmtExpr.Identifier (mkId target))
    let value' := translateExpr value
    wm (.Assign [target'] value')
  | .Return _ value =>
    let value' := translateExpr value
    wm (.Return (some value'))
  | .Block _ stmts =>
    let stmts' := stmts.toList.map translateStmt
    wm (.Block stmts' none)
  | .IfElse _ cond thenBranch elseBranch =>
    let cond' := translateExpr cond
    let then' := translateStmt thenBranch
    let else' := elseBranch.map translateStmt
    wm (.IfThenElse cond' then' else')

/-! ## Translate a Calc function to a Laurel Procedure -/

def translateFunction : Calc.Command SourceRange → Except String Procedure
  | .Function _ name params returns contracts body => do
    let inputs := params.toList.map fun
      | .Param _ n t => { name := mkId n, type := translateType t : Parameter }
    let outputs := returns.toList.map fun
      | .Param _ n t => { name := mkId n, type := translateType t : Parameter }
    let preconditions := contracts.toList.filterMap fun
      | .Requires _ cond => some (translateExpr cond)
      | _ => none
    let postconditions := contracts.toList.filterMap fun
      | .Ensures _ cond => some (translateExpr cond)
      | _ => none
    let body' := translateStmt body
    return {
      name := mkId name
      inputs := inputs
      outputs := outputs
      preconditions := preconditions
      determinism := .deterministic none
      decreases := none
      isFunctional := false
      body := .Opaque postconditions (some body') []
      md := md
    }

/-! ## Read a serialized Calc program and build a Laurel Program -/

def readCalcProgram (bytes : ByteArray) : Except String Laurel.Program := do
  if !Ion.isIonFile bytes then
    throw "Not an Ion file"
  let pgm ← match Strata.Program.fromIon Calc.Calc_map Calc.Calc.name bytes with
    | .ok p => pure p
    | .error msg => throw s!"Ion parse error: {msg}"
  let mut procedures : List Procedure := []
  for cmd in pgm.commands do
    match Calc.Command.ofAst cmd with
    | .ok fn => do
      let proc ← translateFunction fn
      procedures := procedures ++ [proc]
    | .error msg => throw s!"AST error: {msg}"
  return {
    staticProcedures := procedures
    staticFields := []
    types := []
  }

end Strata.Calc
```

## Step 5: Run verification

Create a small executable that ties everything together. Create `CalcVerify.lean` at the repo root:

```lean
/-
  CalcVerify: verify a Calc program via the Laurel pipeline.
-/
import Strata.Languages.Calc.Calc

open Strata

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let bytes ← IO.FS.readBinFile ⟨file⟩
    match Calc.readCalcProgram bytes with
    | .error msg =>
      IO.println s!"Error: {msg}"
      return 1
    | .ok laurelProgram =>
      let (vcResultsOpt, diagnostics) ←
        Laurel.verifyToVcResults laurelProgram
      -- Print diagnostics (translation warnings/errors)
      for diag in diagnostics do
        IO.println s!"Diagnostic: {repr diag}"
      -- Print verification results
      match vcResultsOpt with
      | none =>
        IO.println "Translation to Core failed."
        return 1
      | some vcResults =>
        for vcResult in vcResults do
          let marker := if vcResult.isSuccess then "✔" else "✗"
          IO.println s!"{marker} [{vcResult.obligation.label}]: {vcResult.formatOutcome}"
        let success := vcResults.all Core.VCResult.isSuccess
        if success then
          IO.println s!"All {vcResults.size} goals passed."
          return 0
        else
          let failed := (vcResults.filter Core.VCResult.isNotSuccess).size
          IO.println s!"{failed} goal(s) failed."
          return 1
  | _ =>
    IO.println "Usage: CalcVerify <file.calc.ion>"
    return 1
```

Register the executable in `lakefile.toml`:

```toml
[[lean_exe]]
name = "CalcVerify"
root = "CalcVerify"
```

Now run the full pipeline:

```bash
# Step 1: Parse and serialize
python Tools/Calc/calc_dialect.py Examples/Abs.calc

# Step 2: Build and verify
lake build CalcVerify
lake exe CalcVerify Examples/Abs.calc.ion
```

Expected output:

```
✔ [abs/ensures/0]: verified
All 1 goals passed.
```

### Try a failing program

Create `Examples/AbsBug.calc`:

```
function abs_bug(x: int) returns (result: int)
  requires true
  ensures result >= 0
{
  result := x
}
```

```bash
python Tools/Calc/calc_dialect.py Examples/AbsBug.calc
lake exe CalcVerify Examples/AbsBug.calc.ion
```

Expected output:

```
✗ [abs_bug/ensures/0]: counterexample found
  x = -1, result = -1
1 goal(s) failed.
```

The SMT solver found that when `x = -1`, the postcondition `result >= 0` is violated.

## What just happened?

Here's the full data flow:

```
Abs.calc                          (Calc source text)
  │  Python parser (Step 2)
  ▼
Calc AST (DDM Operations)         (in-memory Python objects)
  │  Ion serialization (Step 3)
  ▼
Abs.calc.ion                      (binary Ion file on disk)
  │  Lean deserializer (Step 4)
  ▼
Calc typed AST                    (Lean inductive types, auto-generated by #strata_gen)
  │  CalcToLaurel translator (Step 4)
  ▼
Laurel Program                    (Laurel.Procedure, Laurel.StmtExprMd, etc.)
  │  Laurel → Core (existing pipeline)
  ▼
Core Program                      (Core.Procedure, Core.Statement, etc.)
  │  VCG + SMT encoding (existing pipeline)
  ▼
SMT queries                       (sent to cvc5)
  │
  ▼
Verification results              (verified / counterexample)
```

The key insight: you only wrote the Calc-specific parts (dialect definition, parser, translator to Laurel). Everything from Laurel onward — the Core translation, verification condition generation, SMT encoding, and solver interaction — is reused from Strata's existing infrastructure.

## Next steps

- **[Front-End Guide](frontend_guide.md)** — Architecture decisions, dialect selection, translation concepts, and the full implementation API reference.
- **[Hosting & Governance](frontend_hosting.md)** — Where to host your front-end and how to structure the codebase.
- **[Testing & Validation](frontend_testing.md)** — Differential testing, coverage targets, and debugging.
