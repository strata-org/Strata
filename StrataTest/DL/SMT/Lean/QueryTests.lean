/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.Lean.Query
meta import StrataTest.Util.LeanExport
meta import Lean
meta import Strata.DL.Imperative.SMTUtils

meta section

open Lean Strata SMT LeanExport Elab Command Core.LeanExport.Tests

private def intConst (name : String) : UF :=
  { id := name, args := [], out := .int }

/-- The term that applies `uf` to no arguments: a constant. -/
private def call (uf : UF) : SMT.Term := .app (.uf uf) [] uf.out

private def equality (a b : SMT.Term) : SMT.Term :=
  .app .eq [a, b] .bool

-- These fixtures exercise preparation through the same API as the export.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let x := intConst "x"
  let q ← prepare {} [] (equality (call x) (call x))
    [] [{ name := "x", ty := .int }]
  unless q.context.ufs.size == 1 do throwError "missing declared symbol"
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ x : Int, x = x)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "the declared variable was not closed over as `∀ x : Int, x = x`"
  Meta.check q.validity

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let x := intConst "x"
  let y := intConst "y"
  let z := intConst "z"
  let q ← prepare
    { ufs := .ofArray #[x, y] } [] (equality (call z) (call x))
    [{ name := "y", ty := .int, body := call x },
     { name := "z", ty := .int, body := call y }] []
  unless q.context.ufs.size == 1 && q.context.ifs.size == 2 do
    throwError "ordered definitions or shadowing lost"
  Meta.check q.validity

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let x := intConst "x"
  let axm := equality (call x) (.int 3)
  let q ← prepare
    { ufs := .ofArray #[x], axms := .ofArray #[axm] } [] (.bool true) [] []
  unless q.context.axms.toArray == #[axm] && q.context.ufs.size == 1 do
    throwError "an axiom or its symbol was dropped"
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ x : Int, x = 3 → True)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "context axiom missing from the translated proposition"

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let x := intConst "x"
  let q ← prepare { ufs := .ofArray #[x] }
    [.app .le [.int 0, call x] .bool]
    (.app .lt [.int 0, call x] .bool) [] []
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ x : Int, 0 ≤ x → 0 < x)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "assumption-to-goal translation changed"

-- Division and modulo by a literal zero are not folded: SMT-LIB leaves their value open.
#guard Factory.intDiv (.int 7) (.int 0) == .app .div [.int 7, .int 0] .int
#guard Factory.intMod (.int 7) (.int 0) == .app .mod [.int 7, .int 0] .int
#guard Factory.intDiv (.int 7) (.int 2) == .int 3
#guard Factory.intMod (.int 7) (.int 2) == .int 1

-- Preparation leaves a division or modulo by zero as it is; the translator gives it its meaning:
-- the proposition quantifies over `divByZero` and `modByZero` and reads `x div y` as
-- `if y = 0 then divByZero x else x / y`. The claim `7 div 0 = 0` is then not provable, as it
-- is not valid for the solver.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let d : SMT.Term := .app .div [.int 7, .int 0] .int
  let q ← prepare {} [] (equality d (.int 0)) [] []
  unless q.goal == equality d (.int 0) do
    throwError "preparation changed a division by zero: {repr q.goal}"
  unless q.context.ufs.size == 0 && q.context.ifs.size == 0 do
    throwError "preparation declared or defined a symbol for a division"
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ divByZero _modByZero : Int → Int,
    (if (0 : Int) = 0 then divByZero 7 else 7 / 0) = 0)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "a division by zero is not read with `divByZero`: {q.validity}"
  let m : SMT.Term := .app .mod [.int 7, .int 0] .int
  let q ← prepare {} [] (equality m (.int 0)) [] []
  unless q.goal == equality m (.int 0) do
    throwError "preparation changed a modulo by zero: {repr q.goal}"
  unless q.context.ufs.size == 0 && q.context.ifs.size == 0 do
    throwError "preparation declared or defined a symbol for a modulo"
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ _divByZero modByZero : Int → Int,
    (if (0 : Int) = 0 then modByZero 7 else 7 % 0) = 0)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "a modulo by zero is not read with `modByZero`: {q.validity}"

#eval show CommandElabM Unit from runTermElabM fun _ => do
  -- A query without division or modulo is translated without `divByZero` and `modByZero`.
  let x := intConst "x"
  let q ← prepare { ufs := .ofArray #[x] } []
    (equality (.app .add [call x, .int 1] .int) (.app .add [.int 1, call x] .int)) [] []
  unless q.context.ufs.size == 1 && q.context.ifs.size == 0 do
    throwError "preparation added a symbol to a query without division or modulo"
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ x : Int, x + 1 = 1 + x)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "a query without division or modulo binds more than its symbol: {q.validity}"

#eval show CommandElabM Unit from runTermElabM fun _ => do
  -- Nested divisions and modulos in the goal, a modulo in an axiom and a division in the body of
  -- a definition of the obligation are left as they are, and preparation declares nothing else.
  let x := intConst "x"
  let y := intConst "y"
  let d := intConst "d"
  let nested := .app .mod [.app .div [.app .div [call x, call y] .int, call y] .int, call x] .int
  let axm := equality (.app .mod [call y, call x] .int) (.int 0)
  let dBody := .app .div [call x, call y] .int
  let q ← prepare
    { ufs := .ofArray #[x, y], axms := .ofArray #[axm] } [] (equality nested (call d))
    [{ name := "d", ty := .int, body := dBody }] []
  unless q.goal == equality nested (call d) do
    throwError "nested divisions and modulos were changed: {repr q.goal}"
  unless q.context.axms.toArray == #[axm] do
    throwError "the modulo in an axiom was changed: {repr q.context.axms.toArray}"
  unless q.context.ifs.toArray == #[{ id := "d", args := [], out := .int, body := dBody }] do
    throwError "the division in a definition was changed: {repr q.context.ifs.toArray}"
  unless q.context.ufs.toArray == #[x, y] do
    throwError "preparation declared other symbols: {repr q.context.ufs.toArray}"
  Meta.check q.validity

#eval show CommandElabM Unit from runTermElabM fun _ => do
  -- Preparation adds no names of its own and renames nothing: a query with a division and a
  -- modulo whose symbols, definitions, declarations and binders have names such as `_smt_div_0`
  -- is prepared as it is.
  let taken := ["_smt_div_0", "_smt_mod_0", "_smt_x_0", "_smt_y_0", "_smt_div0_0", "_smt_mod0_0"]
  let used := taken.map intConst
  let sum := used.foldl (fun t v => .app .add [t, call v] .int) (.int 0)
  let goal := equality (.app .mod [.app .div [sum, call used[0]!] .int, call used[1]!] .int)
    (.int 0)
  let q ← prepare { ufs := .ofArray used.toArray } [] goal [] []
  unless q.goal == goal && q.context.ifs.size == 0 do
    throwError "a query with names like `_smt_div_0` was changed: {repr q.goal}"
  unless q.context.ufs.toArray == used.toArray do
    throwError "the query's own symbols were renamed: {repr q.context.ufs.toArray}"
  Meta.check q.validity
  -- The same names for definitions and for managed declarations.
  let x := intConst "x"
  let named (name : String) := call (intConst name)
  let goal := equality
    (.app .mod [.app .div [call x, named "_smt_div_0"] .int, named "_smt_y_0"] .int)
    (.app .add [named "_smt_mod_0", named "_smt_mod0_0"] .int)
  let q ← prepare
    { ufs := .ofArray #[x, intConst "_smt_x_0", intConst "_smt_div0_0"] } [] goal
    [{ name := "_smt_div_0", ty := .int,
       body := .app .div [named "_smt_x_0", named "_smt_div0_0"] .int },
     { name := "_smt_mod0_0", ty := .int, body := .int 1 }]
    [{ name := "_smt_y_0", ty := .int }, { name := "_smt_mod_0", ty := .int }]
  unless q.goal == goal do
    throwError "a query with definitions like `_smt_div_0` was changed: {repr q.goal}"
  unless q.context.ufs.toArray.map (·.id) ==
      #["x", "_smt_x_0", "_smt_div0_0", "_smt_y_0", "_smt_mod_0"] do
    throwError "declared symbols were renamed: {repr q.context.ufs.toArray}"
  unless q.context.ifs.toArray.map (·.id) == #["_smt_div_0", "_smt_mod0_0"] do
    throwError "definitions were renamed: {repr q.context.ifs.toArray}"
  Meta.check q.validity
  -- The same names for a quantified variable and a definition parameter.
  let v : TermVar := ⟨"_smt_div_0", .int⟩
  let p : TermVar := ⟨"_smt_x_0", .int⟩
  let g : SMT.IF := { id := "g", args := [p], out := .int, body := .app .mod [.var p, .int 2] .int }
  let goal := .quant .all [v] [] (equality (.app .div [.var v, call x] .int)
    (.app (.uf g.toUF) [.app .mod [call x, .int 2] .int] .int))
  let q ← prepare { ufs := .ofArray #[x], ifs := .ofArray #[g] } [] goal [] []
  unless q.goal == goal && q.context.ifs.toArray == #[g] do
    throwError "a query binding names like `_smt_div_0` was changed: {repr q.goal}"
  Meta.check q.validity

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let q ← prepare {} []
    (equality (.app .bvudiv [.bitvec (7 : BitVec 8), .bitvec (0 : BitVec 8)]
      (.bitvec 8)) (.bitvec (255 : BitVec 8))) [] []
  let proof ← Meta.mkDecideProof q.validity
  Meta.check proof

/-- Run `action` and require that it fails with a message that contains `expected`. -/
private def rejects (expected : String) (action : MetaM PreparedQuery) : MetaM Unit := do
  let rejected ← try
      let _ ← action
      pure false
    catch e =>
      let message ← e.toMessageData.toString
      unless (message.splitOn expected).length > 1 do
        throwError "Expected rejection containing '{expected}', got:\n{message}"
      pure true
  unless rejected do throwError "Query unexpectedly accepted: {expected}"

/-- Prove `prop` by `intros; rfl` and require a complete proof: the tactic runs at once (it is not
postponed), and the proof has no open goal and no `sorry` and type-checks. -/
private def provesByIntrosRfl (prop : Expr) : Elab.Term.TermElabM Unit :=
  Elab.Term.withoutErrToSorry do
    let proof ← Elab.Term.elabTermEnsuringType (← `(by intros; rfl)) prop
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasSorry then
      throwError "the proof of {prop} by `intros; rfl` is not complete"
    Meta.check proof

-- The helper refuses a false proposition, so the cases that use it check what they prove.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let wrong ← Elab.Term.elabTerm (← `(∀ x : Nat, x = x + 1)) none
  let refused ← try provesByIntrosRfl wrong; pure false catch _ => pure true
  unless refused do throwError "a false proposition was proved by `intros; rfl`"

-- A name both declared and defined is refused, since the solver's encoders do not send the
-- definition then (or reject the query); a context symbol that the obligation defines, as a
-- common subexpression is, is stated with its definition, as the encoders send it.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let x := intConst "x"
  let five : SMT.IF := { id := "x", args := [], out := .int, body := .int 5 }
  rejects "has the name of a definition in the context" (prepare { ifs := .ofArray #[five] } []
    (equality (call x) (.int 5)) [] [{ name := "x", ty := .int }])
  rejects "has the name of a declaration" (prepare {} [] (equality (call x) (.int 5))
    [{ name := "x", ty := .int, body := .int 5 }] [{ name := "x", ty := .int }])
  let q ← prepare { ufs := .ofArray #[x] } [] (equality (call x) (.int 5))
    [{ name := "x", ty := .int, body := .int 5 }] []
  unless q.context.ufs.size == 0 && q.context.ifs.size == 1 do
    throwError "a defined context symbol is not stated by its definition"
  let expected ← Lean.Elab.Term.elabTerm (← `(have x : Int := 5; x = 5)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "a defined context symbol is not stated by its definition"

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let f := intConst "f"
  let v : TermVar := ⟨"f", .int⟩
  let ambiguous := .quant .exist [v] []
    (.app .not [equality (call f) (.var v)] .bool)
  -- SMT reads both occurrences as the bound f. Translating the UF as an
  -- independent global instead would turn this false goal into a valid one.
  for (assumptions, goal, axioms) in
      [([], ambiguous, []), ([ambiguous], .bool true, []),
       ([], .bool true, [ambiguous])] do
    rejects "shadowed by an SMT binder" (prepare
      { ufs := .ofArray #[f], axms := .ofArray axioms.toArray }
      assumptions goal [] [])
  let defined : SMT.IF := {
    id := "g", args := [v], out := .int, body := call f }
  rejects "shadowed by an SMT binder" (prepare
    { ufs := .ofArray #[f], ifs := .ofArray #[defined] } []
    (equality (.app (.uf defined.toUF) [.int 0] .int) (.int 0)) [] [])
  let inner : TermVar := ⟨"f", .bool⟩
  rejects "nearest SMT binder" (prepare {} []
    (.quant .all [v] [] (.quant .all [inner] []
      (equality (.var v) (.var v)))) [] [])
  let q ← prepare {} []
    (.quant .all [v] [] (.quant .all [inner] []
      (equality (.var inner) (.var inner)))) [] []
  provesByIntrosRfl q.validity

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let v : TermVar := ⟨"true", .bool⟩
  rejects "shadowed by an SMT binder" (prepare {} []
    (.quant .exist [v] []
      (.app .not [equality (.bool true) (.var v)] .bool)) [] [])
  -- A declared function with the name of a constant: no binder, and the diagnostic says so.
  let f : UF := { id := "true", args := [], out := .bool }
  rejects "Symbol 'true' is also the name of a function the query declares or defines" (prepare
    { ufs := .ofArray #[f] } [] (equality (call f) (.bool true)) [] [])
  let v : TermVar := ⟨"none", .option .int⟩
  rejects "shadowed by an SMT binder" (prepare {} []
    (.quant .exist [v] [] (equality (.none .int) (.var v))) [] [])
  let v : TermVar := ⟨"not", .bool⟩
  rejects "shadowed by an SMT binder" (prepare {} []
    (.quant .exist [v] [] (.app .not [.var v] .bool)) [] [])
  -- Escaping keeps this variable distinct from the actual addition operator.
  let v : TermVar := ⟨"+", .int⟩
  let sum := .app .add [.var v, .int 1] .int
  let q ← prepare {} []
    (.quant .all [v] [] (equality sum sum)) [] []
  provesByIntrosRfl q.validity

#eval show CommandElabM Unit from runTermElabM fun _ => do
  rejects "Conflicting managed" (prepare
    { ufs := .ofArray #[intConst "x"] } [] (.bool true)
    [] [{ name := "x", ty := .bool }])
  rejects "Duplicate definition" (prepare {} [] (.bool true)
    [{ name := "x", ty := .int, body := .int 0 },
     { name := "x", ty := .int, body := .int 1 }] [])
  -- A function the context does not list is declared on first use, as the solver's encoder
  -- declares it; a second signature for a listed name is still refused.
  let q ← prepare {} []
    (equality (call (intConst "missing")) (.int 0)) [] []
  unless q.context.ufs.toArray.any (·.id == "missing") do
    throwError "a function applied without a declaration was not declared on first use"
  rejects "Missing function" (prepare
    { ufs := .ofArray #[intConst "f"] } []
    (equality (call { id := "f", args := [], out := .bool }) (.bool true)) [] [])
  let recursive : SMT.IF := {
    id := "f", args := [], out := .int
    body := .int 0, isRec := true }
  rejects "Recursive define-fun" (prepare
    { ifs := .ofArray #[recursive] } [] (equality (call recursive.toUF) (.int 0)) [] [])

#eval show CommandElabM Unit from runTermElabM fun _ => do
  -- Sort aliases stay in the query for the translator's own `define-sort` handling;
  -- preparation resolves them only to check the sort. A name defined once with the alias and
  -- once with the sort it stands for has two signatures, which the assembly refuses rather than
  -- guesses about.
  let alias : TermType := .constr "Alias" []
  let first : SMT.IF := { id := "f", args := [], out := alias, body := .int 0 }
  let second : SMT.IF := { id := "f", args := [], out := .int, body := .int 1 }
  let ctx : Core.SMT.Context := {
    tySubst := [("Alias", .int)], ifs := .ofArray #[first, second] }
  unless ctx.ifs.size == 2 do throwError "collision fixture lost a definition"
  rejects "Conflicting signature" (prepare ctx []
    (equality (call second.toUF) (.int 1)) [] [])
  let q ← prepare { ctx with ifs := .ofArray #[first] } []
    (equality (call first.toUF) (call first.toUF)) [] []
  unless q.context.ifs.size == 1 && q.context.ifs.toArray[0]!.out == alias do
    throwError "the alias was resolved away instead of being left to the translator"
  provesByIntrosRfl q.validity

-- Datatypes, Option, uninterpreted sorts and arrays are not translated: a
-- query that reaches one is refused with a diagnostic, one that only declares them is not.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let arrayTy : TermType := .constr "Array" [.int, .int]
  let a : UF := { id := "a", args := [], out := arrayTy }
  let index : TermVar := { id := "i", ty := .int }
  let select := .app .select [call a, .var index] .int
  rejects "unsupported sort" (prepare { ufs := .ofArray #[a] } []
    (.quant .all [index] [] (equality select select)) [] [])
  rejects "unsupported sort" (prepare {} []
    (.quant .all [{ id := "a", ty := arrayTy }] [] (.bool true)) [] [])
  rejects "unsupported sort" (prepare
    { tySubst := [("Alias", arrayTy)] } []
    (.quant .all [{ id := "a", ty := .constr "Alias" [] }] [] (.bool true)) [] [])
  let color : TermType := .constr "Color" []
  let red := .app (.datatype_op .constructor "red") [] color
  rejects "unsupported sort" (prepare {} [] (equality red red) [] [])
  let u : UF := { id := "u", args := [], out := .constr "U" [] }
  rejects "unsupported sort" (prepare
    { sorts := .ofArray #[{ name := "U", arity := 0 }], ufs := .ofArray #[u] } []
    (equality (call u) (call u)) [] [])
  rejects "unsupported sort" (prepare {} []
    (equality (.none .int) (.none .int)) [] [])
  let q ← prepare
    { sorts := .ofArray #[{ name := "U", arity := 0 }], ufs := .ofArray #[a, u] } []
    (.bool true) [] []
  unless q.context.ufs.size == 0 do throwError "unreached unsupported declarations were retained"
  unless q.validity.isConstOf ``True do
    throwError "an unreached sort declaration changed the proposition: {q.validity}"

#eval show CommandElabM Unit from runTermElabM fun _ => do
  let bad : UF := { id := "real", args := [], out := .real }
  rejects "unsupported sort" (prepare
    { ufs := .ofArray #[bad] } [] (equality (call bad) (call bad)) [] [])
  rejects "unsupported sort" (prepare
    { ufs := .ofArray #[bad], axms := .ofArray #[equality (call bad) (call bad)] }
    [] (.bool true) [] [])
  let q ← prepare
    { ufs := .ofArray #[bad] } [] (.bool true) [] []
  unless q.context.ufs.size == 0 do throwError "unused unsupported declaration retained"
  let regex : UF := { id := "regex", args := [], out := .regex }
  rejects "regex" (prepare
    { ufs := .ofArray #[regex] } [] (equality (call regex) (call regex)) [] [])
  -- Strings are refused wherever they occur: the solver's strings are not Lean's. That covers
  -- an operation on literals, a literal compared with a literal, a declared string symbol and a
  -- quantified string variable.
  rejects "unsupported sort 'String'" (prepare {} []
    (.app .str_contains [.string "hello", .string "e"] .bool) [] [])
  rejects "unsupported sort 'String'" (prepare {} [] (equality (.string "a") (.string "a")) [] [])
  let str : UF := { id := "s", args := [], out := .string }
  rejects "unsupported sort 'String'" (prepare
    { ufs := .ofArray #[str] } [] (equality (call str) (call str)) [] [])
  let sv : TermVar := ⟨"t", .string⟩
  rejects "unsupported sort 'String'" (prepare {} []
    (.quant .all [sv] [] (equality (.var sv) (.var sv))) [] [])
  -- The diagnostic of an unsupported sort is one line.
  let arr : UF :=
    { id := "a", args := [], out := .constr "Array" [.int, .constr "Array" [.int, .int]] }
  try
    let _ ← prepare { ufs := .ofArray #[arr] } [] (equality (call arr) (call arr)) [] []
    throwError "an array query was accepted"
  catch e =>
    let message ← e.toMessageData.toString
    unless (message.splitOn "unsupported sort").length > 1 && !message.contains '\n' do
      throwError "the unsupported-sort diagnostic is not one line: {message}"

-- A binder shaped like a name the solver's encoder generates (`<name>@<n>`, `f.<n>`) is refused:
-- in the solver's text it could capture the renamed symbol, here it would not. Other names with
-- `@` or `.` are accepted.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let renamed : TermVar := ⟨"abs@1", .int⟩
  let abs := intConst "abs"
  rejects "has the shape of a name the solver's encoder generates" (prepare
    { ufs := .ofArray #[abs] } []
    (.quant .exist [renamed] [] (.app .not [equality (.var renamed) (call abs)] .bool)) [] [])
  let generated : TermVar := ⟨"f.0", .int⟩
  rejects "has the shape of a name the solver's encoder generates" (prepare {} []
    (.quant .all [generated] [] (equality (.var generated) (.var generated))) [] [])
  let plain : TermVar := ⟨"x.y@z", .int⟩
  let q ← prepare {} [] (.quant .all [plain] [] (equality (.var plain) (.var plain))) [] []
  Meta.check q.validity

-- The node bound counts binders: Lean cannot represent a variable that crosses 2^20 binders, so
-- a quantifier over more variables than `maxPreparedNodes` is refused before any pass walks it,
-- and so is a query that declares more symbols than that.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let v : TermVar := ⟨"v", .int⟩
  let wide : SMT.Term :=
    .quant .all (List.replicate (maxPreparedNodes + 1) v) [] (.app .le [.var v, .var v] .bool)
  unless (withinPreparedNodes {} [] wide [] []).toBool == false do
    throwError "a quantifier over more variables than the bound was not refused"
  rejects "too large to export" (prepare {} [] wide [] [])
  let many := (List.range (maxPreparedNodes + 1)).map fun i => intConst s!"c{i}"
  let declared : Core.SMT.Context := { ufs := .ofArrayUnchecked many.toArray }
  unless (withinPreparedNodes declared [] (.bool true) [] []).toBool == false do
    throwError "a query declaring more symbols than the bound was not refused"

-- `distinct` expands into its pairs, conjoined as a balanced tree: forty operands give 780
-- pairs, a conjunction ten levels deep, and the proposition still elaborates. Seven hundred
-- give 244,650 pairs, about 1.2 million nodes, more than the bound allows: refused by the count
-- alone.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let consts (n : Nat) := (List.range n).map fun i => intConst s!"c{i}"
  let q ← prepare { ufs := .ofArray (consts 40).toArray } []
    (.app .distinct ((consts 40).map call) .bool) [] []
  Meta.check q.validity
  let rec depth : SMT.Term → Nat
    | .app (.core .and) [a, b] _ => 1 + max (depth a) (depth b)
    | _ => 0
  unless depth q.goal ≤ 10 do throwError "the conjunction of the pairs is {depth q.goal} deep"
  rejects "too large to export" (prepare { ufs := .ofArray (consts 700).toArray } []
    (.app .distinct ((consts 700).map call) .bool) [] [])

-- `normalizeTerm`, rule by rule. `prepareTerms_sound` proves only the rule for `distinct` of two
-- or more operands (its fragment has no `and`/`or` of fewer than two operands, no chains of
-- three or more operands, no n-ary `div` and no `distinct` of fewer than two operands), so each
-- `#guard` below pins the exact term one rule gives.
private def ix : SMT.Term := call (intConst "x")
private def iy : SMT.Term := call (intConst "y")
private def iz : SMT.Term := call (intConst "z")
private def iw : SMT.Term := call (intConst "w")
private def bp : SMT.Term := call { id := "p", args := [], out := .bool }
private def tv : TermVar := ⟨"v", .int⟩

/-- `¬(a = b)`, the shape of one pair of `distinct`. -/
private def differ (a b : SMT.Term) : SMT.Term := .app .not [equality a b] .bool

-- `and []` is `true`, `or []` is `false`.
#guard normalizeTerm (.app .and [] .bool) == .bool true
#guard normalizeTerm (.app .or [] .bool) == .bool false
-- `and [p]` and `or [p]` are `p`.
#guard normalizeTerm (.app .and [bp] .bool) == bp
#guard normalizeTerm (.app .or [bp] .bool) == bp
-- A chain of three operands is the conjunction of its two links, in order, operands in place.
#guard normalizeTerm (.app .eq [ix, iy, iz] .bool) ==
  .app .and [.app .eq [ix, iy] .bool, .app .eq [iy, iz] .bool] .bool
#guard normalizeTerm (.app .le [ix, iy, iz] .bool) ==
  .app .and [.app .le [ix, iy] .bool, .app .le [iy, iz] .bool] .bool
#guard normalizeTerm (.app .lt [ix, iy, iz] .bool) ==
  .app .and [.app .lt [ix, iy] .bool, .app .lt [iy, iz] .bool] .bool
#guard normalizeTerm (.app .ge [ix, iy, iz] .bool) ==
  .app .and [.app .ge [ix, iy] .bool, .app .ge [iy, iz] .bool] .bool
#guard normalizeTerm (.app .gt [ix, iy, iz] .bool) ==
  .app .and [.app .gt [ix, iy] .bool, .app .gt [iy, iz] .bool] .bool
-- Four operands: three links `x ≤ y`, `y ≤ z`, `z ≤ w`, conjoined as `l₁ ∧ (l₂ ∧ l₃)`, for
-- every chained operator.
#guard normalizeTerm (.app .le [ix, iy, iz, iw] .bool) ==
  .app .and [.app .le [ix, iy] .bool,
    .app .and [.app .le [iy, iz] .bool, .app .le [iz, iw] .bool] .bool] .bool
#guard normalizeTerm (.app .eq [ix, iy, iz, iw] .bool) ==
  .app .and [.app .eq [ix, iy] .bool,
    .app .and [.app .eq [iy, iz] .bool, .app .eq [iz, iw] .bool] .bool] .bool
#guard normalizeTerm (.app .lt [ix, iy, iz, iw] .bool) ==
  .app .and [.app .lt [ix, iy] .bool,
    .app .and [.app .lt [iy, iz] .bool, .app .lt [iz, iw] .bool] .bool] .bool
#guard normalizeTerm (.app .ge [ix, iy, iz, iw] .bool) ==
  .app .and [.app .ge [ix, iy] .bool,
    .app .and [.app .ge [iy, iz] .bool, .app .ge [iz, iw] .bool] .bool] .bool
#guard normalizeTerm (.app .gt [ix, iy, iz, iw] .bool) ==
  .app .and [.app .gt [ix, iy] .bool,
    .app .and [.app .gt [iy, iz] .bool, .app .gt [iz, iw] .bool] .bool] .bool
-- Binary forms are kept.
#guard normalizeTerm (.app .lt [ix, iy] .bool) == .app .lt [ix, iy] .bool
#guard normalizeTerm (.app .div [ix, iy] .int) == .app .div [ix, iy] .int
#guard normalizeTerm (.app .mod [ix, iy] .int) == .app .mod [ix, iy] .int
-- n-ary `div` is a left fold of binary `div`: `div x y z` is `div (div x y) z`.
#guard normalizeTerm (.app .div [ix, iy, iz] .int) ==
  .app .div [.app .div [ix, iy] .int, iz] .int
#guard normalizeTerm (.app .div [ix, iy, iz, iw] .int) ==
  .app .div [.app .div [.app .div [ix, iy] .int, iz] .int, iw] .int
-- `mod` is not normalized: of three operands it stays as it is, for the translator to refuse.
#guard normalizeTerm (.app .mod [ix, iy, iz] .int) == .app .mod [ix, iy, iz] .int
-- `distinct` of two operands is its one pair; of three, `x ≠ y ∧ (x ≠ z ∧ y ≠ z)`.
#guard normalizeTerm (.app .distinct [ix, iy] .bool) == differ ix iy
#guard normalizeTerm (.app .distinct [ix, iy, iz] .bool) ==
  .app .and [differ ix iy, .app .and [differ ix iz, differ iy iz] .bool] .bool
-- Four operands: six pairs, first operand outermost, split three and three (balanced).
#guard normalizeTerm (.app .distinct [ix, iy, iz, iw] .bool) ==
  .app .and [
    .app .and [differ ix iy, .app .and [differ ix iz, differ ix iw] .bool] .bool,
    .app .and [differ iy iz, .app .and [differ iy iw, differ iz iw] .bool] .bool] .bool
-- `distinct` of fewer than two operands (outside `SMTQuery.WF`) has no pairs: `true`.
#guard normalizeTerm (.app .distinct [] .bool) == .bool true
#guard normalizeTerm (.app .distinct [ix] .bool) == .bool true
-- `conjunction` of no term is `true`, of one term that term.
#guard conjunction [] == .bool true
#guard conjunction [bp] == bp
-- The rules apply under other operators and quantifiers, to normalized operands.
#guard normalizeTerm (.app .not [.app .and [.app .or [] .bool] .bool] .bool) ==
  .app .not [.bool false] .bool
#guard normalizeTerm (.quant .all [tv] [] (.app .le [ix, .var tv, iy] .bool)) ==
  .quant .all [tv] [] (.app .and [.app .le [ix, .var tv] .bool, .app .le [.var tv, iy] .bool] .bool)
#guard normalizeTerm (.app .add [.app .div [ix, iy, iz] .int, iw] .int) ==
  .app .add [.app .div [.app .div [ix, iy] .int, iz] .int, iw] .int

/-- `prepareTerms` on a query with no definitions or declarations of the obligation: `none` when
it refuses the query, `some true` when it gives back the goal, the assumptions, the declared
symbols, the definitions and the axioms as they are, `some false` when it changes one of them. -/
private def keeps (context : Core.SMT.Context) (assumptions : List SMT.Term) (goal : SMT.Term) :
    Option Bool :=
  match prepareTerms context assumptions goal [] [] with
  | .ok p => some (p.goal == goal && p.assumptions == assumptions &&
      p.context.ufs.toArray == context.ufs.toArray &&
      p.context.ifs.toArray == context.ifs.toArray &&
      p.context.axms.toArray == context.axms.toArray)
  | .error _ => none

/-- A context that declares the integer constants `names`. -/
private def declaring (names : List String) : Core.SMT.Context :=
  { ufs := .ofArray (names.map intConst).toArray }

private def ia : TermVar := ⟨"a", .int⟩
private def ib : TermVar := ⟨"b", .int⟩
private def unary : UF := { id := "f", args := [.int], out := .int }

-- Preparation leaves a binary integer `div` or `mod` exactly as it is, wherever it occurs: in
-- the goal, in an assumption, in an axiom, in a definition body (over constants or over the
-- parameters), under a quantifier and in its trigger, in the argument of a function, nested, and
-- with a literal zero divisor.
#guard keeps (declaring ["x", "y"]) []
  (equality (.app .div [ix, iy] .int) (.app .mod [ix, iy] .int)) == some true
#guard keeps (declaring ["x", "y"])
  [equality (.app .div [ix, iy] .int) (.int 1), equality (.app .mod [ix, iy] .int) (.int 0)]
  (equality ix iy) == some true
#guard keeps { declaring ["x", "y"] with
    axms := .ofArray #[equality (.app .div [ix, iy] .int) (.app .mod [iy, ix] .int)] } []
  (.bool true) == some true
#guard keeps { declaring ["x", "y"] with ifs := .ofArray #[
    { id := "d", args := [], out := .int, body := .app .div [ix, iy] .int },
    { id := "h", args := [ia, ib], out := .int,
      body := .app .add [.app .div [.var ia, .var ib] .int, .app .mod [.var ia, .var ib] .int]
        .int }] } []
  (equality (call { id := "d", args := [], out := .int })
    (.app (.uf { id := "h", args := [.int, .int], out := .int }) [ix, .int 2] .int)) == some true
#guard keeps (declaring ["x"]) [] (.quant .all [tv] [[.app .div [.var tv, ix] .int]]
  (equality (.app .div [.var tv, ix] .int) (.app .mod [.var tv, ix] .int))) == some true
#guard keeps { ufs := .ofArray #[intConst "x", unary] } []
  (equality (.app (.uf unary) [.app .div [ix, .int 2] .int] .int)
    (.app (.uf unary) [.app .mod [ix, .int 2] .int] .int)) == some true
#guard keeps (declaring ["x", "y"]) []
  (equality (.app .mod [.app .div [.app .div [ix, iy] .int, iy] .int, ix] .int) (.int 0)) ==
  some true
#guard keeps {} []
  (equality (.app .div [.int 7, .int 0] .int) (.app .mod [.int 7, .int 0] .int)) == some true
-- Preparation adds no names of its own, so a query that uses names such as `_smt_div_0` is kept.
#guard keeps (declaring ["_smt_div_0", "_smt_div0_0", "_smt_mod_0", "_smt_x_0"]) []
  (equality (.app .div [call (intConst "_smt_div_0"), call (intConst "_smt_div0_0")] .int)
    (.app .mod [call (intConst "_smt_mod_0"), call (intConst "_smt_x_0")] .int)) == some true
-- `keeps` notices a changed goal, assumption, axiom or definition, and a pruned declaration.
#guard keeps (declaring ["x", "y", "z"]) []
  (equality (.app .div [ix, iy, iz] .int) (.int 1)) == some false
#guard keeps (declaring ["x"]) [.app .and [] .bool] (equality ix ix) == some false
#guard keeps { declaring ["x"] with axms := .ofArray #[.app .and [equality ix ix] .bool] } []
  (.bool true) == some false
#guard keeps { declaring ["x"] with
    ifs := .ofArray #[{ id := "d", args := [], out := .bool, body := .app .or [] .bool }] } []
  (equality (call { id := "d", args := [], out := .bool }) (equality ix ix)) == some false
#guard keeps (declaring ["x", "y"]) [] (equality ix ix) == some false

-- In a query, an n-ary `div` becomes nested binary `div`s: three operands in the goal and in a
-- definition body, four in an assumption and in an axiom.
#guard match prepareTerms { declaring ["x", "y", "z", "w"] with
    axms := .ofArray #[equality (.app .div [ix, iy, iz, iw] .int) (.int 1)] }
    [equality (.app .div [ix, iy, iz, iw] .int) (.int 0)]
    (equality (.app .div [ix, iy, iz] .int) (call (intConst "d")))
    [{ name := "d", ty := .int, body := .app .div [ix, iy, iz] .int }] [] with
  | .ok p =>
    let three := .app .div [.app .div [ix, iy] .int, iz] .int
    let four := .app .div [three, iw] .int
    p.goal == equality three (call (intConst "d")) &&
      p.assumptions == [equality four (.int 0)] &&
      p.context.axms.toArray == #[equality four (.int 1)] &&
      p.context.ifs.toArray.map (·.body) == #[three]
  | .error _ => false

#eval show CommandElabM Unit from runTermElabM fun _ => do
  -- Through `prepare`, so that the translator runs: an n-ary division becomes nested binary
  -- divisions, the inner one first, each read with `divByZero`; a division in the argument of
  -- an uninterpreted function stays there.
  let x := intConst "x"
  let y := intConst "y"
  let z := intConst "z"
  let q ← prepare { ufs := .ofArray #[x, y, z] } []
    (equality (.app .div [call x, call y, call z] .int) (.int 1)) [] []
  unless q.goal == equality (.app .div [.app .div [call x, call y] .int, call z] .int) (.int 1) do
    throwError "n-ary division did not become nested binary divisions: {repr q.goal}"
  let expected ← Lean.Elab.Term.elabTerm (← `(∀ divByZero _modByZero : Int → Int, ∀ x y z : Int,
    (if z = 0 then divByZero (if y = 0 then divByZero x else x / y)
      else (if y = 0 then divByZero x else x / y) / z) = 1)) none
  unless ← Meta.isDefEq q.validity expected do
    throwError "the nested divisions are not read with `divByZero`: {q.validity}"
  let f : UF := { id := "f", args := [.int], out := .int }
  let goal := equality (.app (.uf f) [.app .div [call x, .int 2] .int] .int) (.int 0)
  let q ← prepare { ufs := .ofArray #[x, f] } [] goal [] []
  unless q.goal == goal do
    throwError "the division in a function argument was changed: {repr q.goal}"
  Meta.check q.validity
  -- `mod` of three operands is not normalized, and the translator refuses it.
  rejects "'mod' expects exactly two operands, got '3'" (prepare { ufs := .ofArray #[x, y, z] } []
    (equality (.app .mod [call x, call y, call z] .int) (.int 0)) [] [])

-- A `distinct` whose pairs alone pass the bound is refused before its operands are visited.
-- Visiting 2,000 operands would allocate at least one result per operand; the refusal
-- allocates next to nothing. The term passes through a reference, so that the compiler
-- builds it before the measurement starts and cannot build or count it ahead of time.
#eval show IO Unit from do
  let width ← IO.mkRef 2000
  let n ← width.get
  let built ← IO.mkRef (SMT.Term.app .distinct
    ((List.range n).map fun i => call (intConst s!"c{i}")) .bool)
  let wide ← built.get
  let before ← IO.getNumHeartbeats
  unless (normalizedNodes maxPreparedNodes wide).isNone do
    throw (IO.userError "a distinct of 2,000 operands was not refused")
  let used := (← IO.getNumHeartbeats) - before
  unless used < 1000 do
    throw (IO.userError s!"refusing a wide distinct visited its operands: {used} allocations")
  -- The positive control: the same measurement around an `and` of 2,000 operands, which are
  -- visited, counts at least 10,000 allocations, far more than the 1,000 the refusal may use,
  -- so the measurement does notice a visit.
  let built ← IO.mkRef (SMT.Term.app .and
    ((List.range n).map fun i => equality (call (intConst s!"c{i}")) (.int 0)) .bool)
  let conj ← built.get
  let before ← IO.getNumHeartbeats
  unless (normalizedNodes maxPreparedNodes conj).isSome do
    throw (IO.userError "an and of 2,000 operands was refused")
  let used := (← IO.getNumHeartbeats) - before
  unless used ≥ 10000 do
    throw (IO.userError s!"visiting 2,000 operands counted only {used} allocations")

-- Aliases that name one another are refused, directly and through a compound sort; a long
-- chain that ends in a sort is resolved.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let a : UF := { id := "a", args := [], out := .constr "A" [] }
  for tySubst in [[("A", .constr "A" [])], [("A", .constr "B" []), ("B", .constr "A" [])],
      [("A", .option (.constr "B" [])), ("B", .constr "A" [])]] do
    rejects "Cyclic sort alias" (prepare { ufs := .ofArray #[a], tySubst } []
      (equality (call a) (call a)) [] [])
  let chain : List (String × TermType) := (List.range 20000).map fun i =>
    (s!"A{i}", if i == 0 then .int else .constr s!"A{i - 1}" [])
  let a : UF := { id := "a", args := [], out := .constr "A19999" [] }
  match resolveSort { tySubst := chain } a.out with
  | .ok ty => unless ty == .int do throwError "a chain of 20,000 aliases resolved to {repr ty}"
  | .error e => throwError "a chain of 20,000 aliases was not resolved: {e}"

-- Two quantified variables of one name in one quantifier, and two parameters of one name in a
-- definition, are refused.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let v : TermVar := ⟨"v", .int⟩
  rejects "Duplicate SMT quantifier binder" (prepare {} []
    (.quant .all [v, v] [] (equality (.var v) (.var v))) [] [])
  let g : SMT.IF := { id := "g", args := [v, v], out := .int, body := .var v }
  rejects "Duplicate SMT parameter in 'g'" (prepare { ifs := .ofArray #[g] } []
    (equality (.app (.uf g.toUF) [.int 0, .int 1] .int) (.int 0)) [] [])

-- A sort alias defined twice is refused: the query's lookup would take the first definition and
-- the translator the last.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let a : UF := { id := "a", args := [], out := .constr "A" [] }
  rejects "Duplicate sort alias" (prepare
    { ufs := .ofArray #[a], tySubst := [("A", .int), ("A", .bool)] } []
    (equality (call a) (call a)) [] [])

-- An alias defined by another is reached through it, however long the chain, and an alias the
-- query does not reach is dropped.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  -- Each alias is defined by the one before it, as the translator introduces them in order.
  let chain : List (String × TermType) :=
    (List.range 50).map fun i => (s!"A{i}", if i == 0 then .int else .constr s!"A{i - 1}" [])
  let a : UF := { id := "a", args := [], out := .constr "A49" [] }
  let q ← prepare { ufs := .ofArray #[a], tySubst := chain ++ [("Unused", .bool)] } []
    (equality (call a) (call a)) [] []
  unless q.context.tySubst.length == 50 do
    throwError "the alias chain is not reached whole: {q.context.tySubst.length} aliases"
  Meta.check q.validity

-- The node bound counts sort aliases as binders.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let aliases := (List.range (maxPreparedNodes + 1)).map fun i => (s!"A{i}", TermType.int)
  unless (withinPreparedNodes { tySubst := aliases } [] (.bool true) [] []).toBool == false do
    throwError "a query with more sort aliases than the bound was not refused"

-- A String that occurs only in a trigger is refused, although the translator drops triggers:
-- the sort check visits them (fail closed). A String in the body is refused too.
#eval show CommandElabM Unit from runTermElabM fun _ => do
  let v : TermVar := ⟨"v", .int⟩
  rejects "unsupported sort 'String'" (prepare {} []
    (.quant .all [v] [[.app .eq [.string "a", .string "a"] .bool]] (equality (.var v) (.var v)))
    [] [])
  rejects "unsupported sort 'String'" (prepare {} []
    (.quant .all [v] [] (equality (.string "a") (.string "a"))) [] [])

end
