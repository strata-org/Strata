/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Each module is imported plain, for `writeFiles`, which
-- `test_structs_globals_e2e.sh` runs, and `meta`, for the `#guard`s below.
public import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
public import Strata.Backends.CBMC.GOTO.DefaultSymbols
public import Strata.Util.Json
public meta import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
public meta import Strata.Backends.CBMC.GOTO.DefaultSymbols
public meta import Strata.Util.Json

/-! # End-to-end test: hand-built GOTO with structs, pointers and globals

Builds one `CProverGOTO.Context` per function by hand and writes the
`symtab.json` and `goto.json` that `symtab2gb` reads:

- a struct `S {a : unsignedbv 32; b : unsignedbv 32}`; `main` allocates one `S`
  through a `void*` temporary and a typecast, writes `p->a := 3`, and asserts
  `p->a == 3` (holds) and `p->a == 4` (fails);
- a static global `g : unsignedbv 32` initialised to 0, asserted 0 on entry,
  written by `set_g` (a call without a left-hand side) and read by `get_g`;
- a function `mk` returning a two-member struct `Pair` built in a local;
- a second entry `arrays` that reads an array of size 10 indexed with a
  bit-vector, one indexed with `integer`, and an unbounded array, inside and
  outside their bounds.

The `#guard`s below check the JSON. `test_structs_globals_e2e.sh` runs
`writeFiles`, then `symtab2gb` and
`cbmc --function main --no-standard-checks --validate-goto-model`, and checks
the verdict of each assertion; then `cbmc --function arrays` with
`--bounds-check`, and checks that CBMC accepts the reads inside the bounds and
rejects the ones outside, so that the sizes are read as written. -/

namespace CProverGOTO.E2E_StructsGlobals

open CProverGOTO

public section

/-- The name of the module the symbols belong to. -/
def moduleName : String := "e2e"

/-- The 32-bit unsigned bit-vector type. -/
def u32 : Ty := .UnsignedBV 32

/-- The struct allocated by `main`. -/
def sDef : StructDef := { name := "S", components := [("a", u32), ("b", u32)] }

/-- The struct returned by `mk`. -/
def pairDef : StructDef := { name := "Pair", components := [("x", u32), ("y", u32)] }

/-- The global variable. -/
def g : Expr := Expr.symbol "g" u32

/-- The `unsignedbv 32` constant `n`. -/
def c32 (n : Nat) : Expr := Expr.constant (toString n) u32

/-- The source location of an assertion in `fn`, whose description is `comment`. -/
def assertLoc (fn : String) (line : Nat) (comment : String) : SourceLocation :=
  { file := "e2e.goto", line, function := fn, workingDir := "", comment }

/-- Number the instructions of a function body in order. -/
def body (insts : List Instruction) : Array Instruction :=
  (insts.mapIdx fun i inst => { inst with locationNum := i }).toArray

/-- `set_g()`: `g := 5`. -/
def setG : CoreToGOTO.CProverGOTO.Context :=
  { program := { name := "set_g", instructions := body [
      { type := .ASSIGN, code := Code.assign g (c32 5) },
      { type := .END_FUNCTION }] },
    locals := [], formals := [], ret := .Empty }

/-- `get_g() : unsignedbv 32`: returns `g`. -/
def getG : CoreToGOTO.CProverGOTO.Context :=
  { program := { name := "get_g", instructions := body [
      { type := .SET_RETURN_VALUE, code := Code.set_return_value g },
      { type := .END_FUNCTION }] },
    locals := [], formals := [], ret := u32 }

/-- `mk(x : unsignedbv 32) : Pair`: returns `{x := x, y := x + 1}`. -/
def mk : CoreToGOTO.CProverGOTO.Context :=
  let x := Expr.symbol (mkFormalSymbol "mk" "x") u32
  let v := Expr.symbol (mkLocalSymbol "mk" "v") pairDef.ty
  { program :=
      { name := "mk"
        parameterIdentifiers := #[mkFormalSymbol "mk" "x"]
        instructions := body [
          { type := .DECL, code := Code.decl v },
          { type := .ASSIGN, code := Code.assign (Expr.member v "x" u32) x },
          { type := .ASSIGN, code := Code.assign (Expr.member v "y" u32) (Expr.add [x, c32 1]) },
          { type := .SET_RETURN_VALUE, code := Code.set_return_value v },
          { type := .END_FUNCTION }] },
    locals := ["v"], formals := [("x", u32)], ret := pairDef.ty,
    localTypes := Std.HashMap.ofList [("v", pairDef.ty)] }

/-- The entry function. -/
def mainFn : CoreToGOTO.CProverGOTO.Context :=
  let voidPtr := Ty.Pointer .Empty
  let sPtr := Ty.Pointer sDef.ty
  let raw := Expr.symbol (mkLocalSymbol "main" "raw") voidPtr
  let p := Expr.symbol (mkLocalSymbol "main" "p") sPtr
  let r := Expr.symbol (mkLocalSymbol "main" "r") u32
  let q := Expr.symbol (mkLocalSymbol "main" "q") pairDef.ty
  let pa := Expr.member (Expr.dereference p sDef.ty) "a" u32
  let alloc := Expr.allocate (Expr.constant "8" (.UnsignedBV 64))
    (Expr.constant "false" .Boolean) voidPtr
  let assert (line : Nat) (comment : String) (c : Expr) : Instruction :=
    { type := .ASSERT, guard := c, sourceLoc := assertLoc "main" line comment }
  let call (lhs : Expr) (callee : String) (ty : Ty) (args : List Expr) : Instruction :=
    { type := .FUNCTION_CALL, code := Code.functionCall lhs (Expr.symbol callee ty) args }
  { program := { name := "main", instructions := body [
      assert 1 "g is 0 on entry" (Expr.eq g (c32 0)),
      { type := .DECL, code := Code.decl raw },
      { type := .ASSIGN, code := Code.assign raw alloc },
      { type := .DECL, code := Code.decl p },
      { type := .ASSIGN, code := Code.assign p (Expr.typecast raw sPtr) },
      { type := .ASSIGN, code := Code.assign pa (c32 3) },
      assert 6 "p->a is 3" (Expr.eq pa (c32 3)),
      assert 7 "p->a is 4" (Expr.eq pa (c32 4)),
      call Expr.nil "set_g" (Ty.mkFunctionType [] .Empty) [],
      { type := .DECL, code := Code.decl r },
      call r "get_g" (Ty.mkFunctionType [] u32) [],
      assert 11 "get_g returns 5" (Expr.eq r (c32 5)),
      { type := .DECL, code := Code.decl q },
      call q "mk" (Ty.mkFunctionType [u32] pairDef.ty) [c32 7],
      assert 14 "mk(7).y is 8" (Expr.eq (Expr.member q "y" u32) (c32 8)),
      { type := .END_FUNCTION }] },
    locals := ["raw", "p", "r", "q"], formals := [], ret := .Empty,
    localTypes := Std.HashMap.ofList
      [("raw", voidPtr), ("p", sPtr), ("r", u32), ("q", pairDef.ty)] }

/-- The 64-bit signed bit-vector type, CBMC's default index type. -/
def i64 : Ty := .SignedBV 64

/-- `unsignedbv 32[10]`, indexed with `signedbv 64`; its size is written in
    hexadecimal (`A`). -/
def bvIndexedTy : Ty := Ty.mkArray u32 (some (.constant 10))

/-- `unsignedbv 32[10]`, indexed with CBMC's `integer`; its size is written in
    decimal (`10`). -/
def intIndexedTy : Ty := Ty.mkArray u32 (some (.constant 10)) (some .Integer)

/-- `unsignedbv 32[infinity]`. -/
def unboundedTy : Ty := Ty.mkArray u32 (some .infinity)

/--
`arrays()`: a second entry, run with `--bounds-check`, so that CBMC compares
each index with the size as it read it: index 9 is inside an array of size 10
and index 10 outside, for the array indexed with a bit-vector and the one
indexed with `integer`; the unbounded array has no upper bound and still
rejects a negative index. The bit-vector array is indexed with locals whose
value CBMC chooses, fixed by an `ASSUME`, so that its checks reach the solver
instead of being simplified away. The other two are indexed with constants:
CBMC's back ends do not decide a check on an `integer` index or on an
unbounded array, and a check on a constant index is decided by simplification
(an index outside the bounds fails, one inside leaves no property).
-/
def arraysFn : CoreToGOTO.CProverGOTO.Context :=
  let var (name : String) (ty : Ty) : Expr := Expr.symbol (mkLocalSymbol "arrays" name) ty
  let a := var "a" bvIndexedTy
  let b := var "b" intIndexedTy
  let c := var "c" unboundedTy
  let r := var "r" u32
  let i9 := var "i9" i64
  let i10 := var "i10" i64
  let decl (e : Expr) : Instruction := { type := .DECL, code := Code.decl e }
  let assume (c : Expr) : Instruction := { type := .ASSUME, guard := c }
  let read (arr idx : Expr) : Instruction :=
    { type := .ASSIGN, code := Code.assign r (Expr.index arr idx u32) }
  { program := { name := "arrays", instructions := body [
      decl a, decl b, decl c, decl r,
      decl i9, assume (Expr.eq i9 (Expr.constant "9" i64)),
      decl i10, assume (Expr.eq i10 (Expr.constant "10" i64)),
      read a i9, read a i10,
      read b (Expr.constant "9" .Integer), read b (Expr.constant "10" .Integer),
      read c (Expr.constant "9" i64), read c (Expr.constant "-1" i64),
      { type := .END_FUNCTION }] },
    locals := ["a", "b", "c", "r", "i9", "i10"], formals := [], ret := .Empty,
    localTypes := Std.HashMap.ofList
      [("a", bvIndexedTy), ("b", intIndexedTy), ("c", unboundedTy), ("r", u32),
       ("i9", i64), ("i10", i64)] }

/-- The functions of the program. -/
def functions : List CoreToGOTO.CProverGOTO.Context := [mainFn, setG, getG, mk, arraysFn]

/--
The symbol table (without CBMC's default symbols) and the GOTO functions.
Each function's `Context.toJson` adds entries for the symbols its body refers
to; the function, global and struct type symbols written afterwards replace
those entries.
-/
def toJson : Except String (Lean.Json × Lean.Json) := do
  let mut symtab : Std.TreeMap.Raw String Lean.Json := {}
  for ctx in functions do
    let json ← CoreToGOTO.CProverGOTO.Context.toJson ctx.program.name ctx
    if let .obj m := json.symtab then
      symtab := m.foldl (fun acc k v => acc.insert k v) symtab
  for ctx in functions do
    let (k, v) := createFunctionSymbol ctx.program.name ctx.formals ctx.ret
    symtab := symtab.insert k (Lean.toJson v)
  let (gk, gv) ← createGlobalSymbol moduleName "g" u32 (c32 0)
  symtab := symtab.insert gk (Lean.toJson gv)
  for s in [sDef, pairDef] do
    let (k, v) := createStructTypeSymbol s moduleName
    symtab := symtab.insert k (Lean.toJson v)
  let goto ← programsToJson (functions.map fun ctx => (ctx.program.name, ctx.program))
  return (Lean.Json.obj symtab, goto)

/-- Write `symtab.json` (with CBMC's default symbols) and `goto.json` to `dir`. -/
def writeFiles (dir : System.FilePath) : IO Unit := do
  let (symtab, goto) ← IO.ofExcept toJson
  let obj := match symtab with | .obj m => m | _ => {}
  writeJsonFile (dir / "symtab.json").toString (wrapSymtab obj moduleName)
  writeJsonFile (dir / "goto.json").toString goto

end -- public section

/-- The entry `name` of the symbol table. -/
private def symbol (name : String) : Lean.Json :=
  match toJson with
  | .ok (symtab, _) => symtab.getObjValD name
  | .error _ => .null

/-- The instructions of the GOTO function `name`. -/
private def instructions (name : String) : Array Lean.Json :=
  match toJson with
  | .ok (_, goto) => match goto.getObjValD "functions" with
    | .arr fns => match fns.find? (·.getObjValD "name" == Lean.Json.str name) with
      | some fn => match fn.getObjValD "instructions" with
        | .arr insts => insts
        | _ => #[]
      | none => #[]
    | _ => #[]
  | .error _ => #[]

-- The JSON is produced without errors.
#guard toJson.toBool

-- `g` is a static-lifetime global with initial value 0.
#guard (symbol "g").getObjValD "isStaticLifetime" == .bool true
#guard (symbol "g").getObjValD "isThreadLocal" == .bool false
#guard ((symbol "g").getObjValD "value").getObjValD "id" == .str "constant"

-- The struct type symbols are declared, and `mk` returns `Pair`.
#guard (symbol "tag-S").getObjValD "isType" == .bool true
#guard (symbol "tag-Pair").getObjValD "type" == structDefToJson pairDef
#guard (((symbol "mk").getObjValD "type").getObjValD "namedSub").getObjValD "return_type"
  == tyToJson pairDef.ty

-- The size of `a` is the `signedbv 64` constant `A`; the size of `b` is the
-- `integer` constant `10`, and `b` carries its index type; `c` is unbounded.
private def sizeOf (name : String) : Lean.Json :=
  (((symbol (mkLocalSymbol "arrays" name)).getObjValD "type").getObjValD "namedSub").getObjValD "size"
#guard (sizeOf "a").getObjValD "id" == .str "constant"
#guard ((sizeOf "a").getObjValD "namedSub").getObjValD "value" == Lean.Json.mkObj [("id", "A")]
#guard ((sizeOf "a").getObjValD "namedSub").getObjValD "type" == tyToJson i64
#guard ((sizeOf "b").getObjValD "namedSub").getObjValD "value" == Lean.Json.mkObj [("id", "10")]
#guard ((sizeOf "b").getObjValD "namedSub").getObjValD "type" == tyToJson .Integer
#guard ((((symbol (mkLocalSymbol "arrays" "b")).getObjValD "type").getObjValD "namedSub")
  |>.getObjValD "#index_type") == tyToJson .Integer
#guard (sizeOf "c").getObjValD "id" == .str "infinity"

-- `main` has 16 instructions; `set_g` is called with a `nil` left-hand side.
#guard (instructions "main").size == 16
#guard (((instructions "main")[8]!).getObjValD "code").getObjValD "sub"
  == .arr #[Lean.Json.mkObj [("id", "nil")],
    (CProverGOTO.exprToJson (Expr.symbol "set_g" (Ty.mkFunctionType [] .Empty))).toOption.get!,
    Lean.Json.mkObj [("id", "arguments"), ("sub", Lean.Json.arr #[])]]

end CProverGOTO.E2E_StructsGlobals
