/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Counterexample.Model
meta import Strata.Languages.Core.Counterexample.ModelToValuation
meta import Strata.Languages.Core.Counterexample.ModelAnonymous
meta import Strata.Languages.Core.Factory
meta import Strata.Languages.Core.Verifier
meta import Strata.DL.Imperative.SMTUtils
meta import StrataTest.DL.SMT.ModelTestHarness

/-! # Solver-model coverage of the VC check, from solver answer to verdict

Each fixture is a solver answer (a `check-sat` verdict and its `get-value` response) and
the obligation it answers. The answer goes through the same stages as in the verifier:
`solverResult` (parsing, `processModel`), `SMT.Result.splitConsts` (the values of the
obligation's interpretable uninterpreted constants, `interpretableConsts`), the lift
(`smtTermToLExpr`, `smtTermIsValue`), the type gate (`checkedModel`), and the VC check
(`runVCCheck` under `withConsts`). No solver runs at test time.

The answers of the *corpus* fixtures are real cvc5 1.3.4 outputs, captured from
`lake build StrataTest` (the module and assertion are named in each fixture). Their
obligations are rebuilt by hand from the captured SMT query and the residuals the VC
check reported: the same path condition, variable definitions and goal, with the
program's `const` declarations as uninterpreted constants of the factory. Every
corpus fixture is checked twice: as above, and with no constant interpreted (the
constants' bindings discarded), printed as `before`. Before the check, each obligation is
type checked as the verifier type checks a program (`Core.typeCheck`), which annotates its
operators with their types (`typeCheckObligation`).

Summary: 25 VC-check fixtures, 21 of which validate (`genuine`). Among those 21 are 16
corpus checks that validate only when the constants are interpreted: each is
`cantValidate` in its `before` run. The other 5 are a partial model, a rational model, the
two controls of the guards, and the control of the type gate. 4 fixtures must not validate:
two guarded constants and a real-arithmetic model are `cantValidate`, and an ill-typed value
that the type gate removes leaves the model `spurious`. Separately, 13 real cvc5 answers (12
with `let`, 1 with a `\u{…}` string escape) keep every readable binding; a parser without
`let` substitution or escape decoding loses their whole model.
-/

meta section

namespace ModelCoverageCR1Test

open Lambda Imperative Imperative.SMT Core Strata.SMT.ModelTestHarness

/-! ## The pipeline -/

/-- The statement of a path-condition entry: a definition is an `init`, an assumption an
    `assume`. -/
private def entryStmt : PathConditionEntry Expression → Except String Statement
  | .varDecl n ty e => .ok (Statement.init n ty e #[])
  | .assumption l e => .ok (Statement.assume l e #[])
  | .distinct l _ => .error s!"distinct entry {l}"

/-- The path-condition entry of an `init` or `assume` statement. -/
private def stmtEntry : Statement → Except String (PathConditionEntry Expression)
  | Statement.init n ty e _ => .ok (.varDecl n ty e)
  | Statement.assume l e _ => .ok (.assumption l e)
  | _ => .error "not a path-condition statement"

/-- `obligation` type checked by `Core.typeCheck` against the built-in functions with the
    signatures of the functions `F` adds to `Core.Factory` as the program's own (`moreFns`, their
    axioms left out), the verifier's type check of a program: the path condition (one `init`
    per definition, one `assume` per assumption) and
    the goal (an `assert` or a `cover`) form the body of a procedure whose inputs are the free
    variables the path condition does not define, at their annotated types. -/
private def typeCheckObligation (F : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression) : Except String (ProofObligation Expression) := do
  let entries := obligation.assumptions.flatten
  let pc ← entries.mapM entryStmt
  let goal := if obligation.property == .cover then
    Statement.cover obligation.label obligation.obligation #[]
    else Statement.assert obligation.label obligation.obligation #[]
  let defined := entries.filterMap fun | .varDecl n _ _ => some n | _ => none
  let exprs := obligation.obligation :: entries.flatMap fun
    | .assumption _ e | .varDecl _ _ (.det e) => [e]
    | _ => []
  let inputs ← (exprs.flatMap LExpr.freeVars).eraseDups.filter (!defined.contains ·.1)
    |>.mapM fun | (x, some ty) => .ok (x, ty) | (x, none) => .error s!"unannotated {x.name}"
  let header : Procedure.Header :=
    { name := ⟨"obligation", ()⟩, typeArgs := [], inputs := inputs, outputs := [] }
  let proc : Procedure := { header, spec := default, body := .structured (pc ++ [goal]) false }
  let extras := (F.toArray.toList.drop Core.Factory.toArray.size).foldl
    (fun G f => G.pushIfNew { f with axioms := [] }) Lambda.Factory.default
  let prog ← (Core.typeCheck .quiet { decls := [.proc proc #[]] } none extras).mapError
    (toString ·.message)
  let some (.proc p _) := prog.decls.head? | .error "no procedure"
  let .structured ss _ := p.body | .error "unstructured body"
  let g ← match ss.getLast? with
    | some (Statement.assert _ g _) | some (Statement.cover _ g _) => pure g
    | _ => .error "no goal"
  let pc ← ss.dropLast.mapM stmtEntry
  return { obligation with assumptions := [pc], obligation := g }

/-- The VC check's verdict on the solver answer `stdout` to `obligation`, type checked
    (`typeCheckObligation`), whose free variables are `vars`. The discharge asks for the
    values of `vars` and, when `interpret` holds, of the constants
    `interpretableConsts F obligation removed`; the VC check then evaluates under those
    constants' values. `cover` selects the satisfiability check (`A ∧ Q`) instead of the
    validity check (`A ∧ ¬Q`). Without `gate`, the model is checked annotated but not
    type-gated (`annotateFlaggedModel` instead of `checkedModel`). -/
private def verdict (F : @Lambda.Factory CoreLParams) (obligation : ProofObligation Expression)
    (vars : List (String × LMonoTy)) (stdout : String) (interpret : Bool := true)
    (removed : List (PathConditionEntry Expression) := []) (cover : Bool := false)
    (gate : Bool := true) : IO String := do
  let obligation ← IO.ofExcept (typeCheckObligation F obligation)
  let consts := if interpret then interpretableConsts F obligation removed else []
  let typed : List Expression.TypedIdent :=
    vars.map (fun (n, ty) => (⟨n, ()⟩, .forAll [] ty)) ++ consts.map fun (c, ty) =>
      (c, .forAll [] ty)
  let r ← match ← readAnswer typed stdout cover with
    | .ok (sat, val) => pure (if cover then sat else val)
    | .error _ => return "solver error"
  let (r, I) := r.splitConsts consts F {}
  let some m := match r with
      | .sat m | .unknown (some m) => some m
      | _ => none
    | return "no model"
  let F := withConsts F I
  let lifted := m.map fun (k, t) => (k, smtTermToLExpr t, smtTermIsValue t)
  let lm := if gate then checkedModel F obligation lifted
    else annotateFlaggedModel F obligation lifted
  return (runVCCheck (extendAnon F (lm.map (·.2.1))) 20000 lm obligation !cover).describe

/-! ## Expressions and factories -/

/-- A variable of type `ty`. -/
private def fv (n : String) (ty : LMonoTy) : Expression.Expr := .fvar default ⟨n, ()⟩ (some ty)

/-- A nullary operator: an uninterpreted constant of the factory. -/
private def cst (n : String) : Expression.Expr := .op default ⟨n, ()⟩ none

/-- A binary operator of the Core factory applied to `a` and `b`. -/
private def op2 (o : String) (a b : Expression.Expr) : Expression.Expr :=
  .app default (.app default (.op default ⟨o, ()⟩ none) a) b

/-- `a ==> b`. -/
private def imp : Expression.Expr → Expression.Expr → Expression.Expr := op2 "Bool.Implies"

/-- An integer literal. -/
private def int (i : Int) : Expression.Expr := .intConst default i

/-- `F` with uninterpreted constants `cs`, each with its type and axioms. -/
private def withDecls (cs : List (String × LMonoTy × List Expression.Expr))
    (F : @Lambda.Factory CoreLParams := Core.Factory) : @Lambda.Factory CoreLParams :=
  cs.foldl (init := F) fun F (n, ty, axioms) =>
    F.pushIfNew (LFunc.mk ⟨n, ()⟩ (inputs := []) (output := ty) (axioms := axioms))

/-- A validity (`assert`) or satisfiability (`cover`) obligation. -/
private def obl (label : String) (entries : List (PathConditionEntry Expression))
    (goal : Expression.Expr) (property : PropertyType := .assert) :
    ProofObligation Expression :=
  { label, property, assumptions := [entries], obligation := goal,
    metadata := MetaData.empty }

/-- A variable definition `name := e` of the path condition. -/
private def define (name : String) (ty : LMonoTy) (e : Expression.Expr) :
    PathConditionEntry Expression :=
  .varDecl ⟨name, ()⟩ (.forAll [] ty) (.det e)

/-! ## Corpus: `RemoveIrrelevantAxioms.lean`, procedures `P`, `Q0`–`Q3`

`const a, b, c, d : bool`. The obligations share the defined names of the query
(`$__cse.0`–`$__cse.5`), two of which read the constants; the goals read the defined
names. cvc5 answers `unknown` (a quantified axiom on `f`) with the same model for all
nine checks. With no constant interpreted, `$__cse.5 := b ==> c` does not reduce, so
each check is `cantValidate`; with the constants valued, every check validates. -/

/-- The factory of `RemoveIrrelevantAxioms.lean`'s constants. -/
private def boolsF : @Lambda.Factory CoreLParams :=
  withDecls (["a", "b", "c", "d"].map (·, .bool, []))

/-- A defined boolean name of the nine queries. -/
private def cse (k : Nat) : Expression.Expr := fv s!"$__cse.{k}" .bool

/-- The shared definitions of the nine queries. -/
private def riaDefs : List (PathConditionEntry Expression) :=
  [define "$__cse.5" .bool (imp (cst "b") (cst "c")),
   define "$__cse.0" .bool (.eq default (fv "x@2" .int) (int 2)),
   define "$__cse.1" .bool (.eq default (fv "x@3" .int) (int 2)),
   define "$__cse.2" .bool (imp (cst "a") (imp (cse 5) (cst "d"))),
   define "$__cse.3" .bool (.eq default (fv "x@4" .int) (int 2)),
   define "$__cse.4" .bool (.eq default (fv "x@1" .int) (int 2))]

/-- The variables of the nine queries. -/
private def riaVars : List (String × LMonoTy) := ["x@1", "x@2", "x@3", "x@4"].map (·, .int)

/-- cvc5's answer to each of the nine queries. -/
private def riaAnswer : String :=
  "unknown\n((d false) (c false) (b false) (a false) (x@2 0) (x@1 0) (x@4 0) (x@3 0))\n"

/-- The nine checks: label, source position, goal. -/
private def riaChecks : List (String × Expression.Expr) :=
  [("a1@763", .eq default (imp (cst "a") (cse 5)) (imp (imp (cst "a") (cst "b")) (cst "c"))),
   ("a4@937", cse 4), ("a5@964", cse 4), ("a6@1048", cse 0), ("a7@1075", cse 0),
   ("a8@1159", cse 1), ("a9@1186", cse 1), ("a10@1270", cse 3), ("a1@1298", cse 3)]

/--
info: a1@763: genuine (before: can't-validate: varDecl RHS did not reduce)
a4@937: genuine (before: can't-validate: varDecl RHS did not reduce)
a5@964: genuine (before: can't-validate: varDecl RHS did not reduce)
a6@1048: genuine (before: can't-validate: varDecl RHS did not reduce)
a7@1075: genuine (before: can't-validate: varDecl RHS did not reduce)
a8@1159: genuine (before: can't-validate: varDecl RHS did not reduce)
a9@1186: genuine (before: can't-validate: varDecl RHS did not reduce)
a10@1270: genuine (before: can't-validate: varDecl RHS did not reduce)
a1@1298: genuine (before: can't-validate: varDecl RHS did not reduce)
-/
#guard_msgs in
#eval show IO Unit from do
  for (label, goal) in riaChecks do
    let o := obl label riaDefs goal
    IO.println s!"{label}: {← verdict boolsF o riaVars riaAnswer} \
      (before: {← verdict boolsF o riaVars riaAnswer (interpret := false)})"

/-! ## Corpus: `UnrollBoundedQuantifiers.lean`, the unrolled obligations on `const n : int`

The path condition fixes `n`, the goal is the unrolled quantifier. With no constant
interpreted, the path condition does not reduce (`n` has no value), so each check is
`cantValidate`; with `n` valued, every check validates. -/

/-- The factory of `UnrollBoundedQuantifiers.lean`'s constant `n`. -/
private def nF : @Lambda.Factory CoreLParams := withDecls [("n", .int, [])]

/-- The seven checks: label and source position, path condition, goal, cvc5's answer,
    and whether it is a satisfiability (`cover`) check. -/
private def ubqChecks : List (String × Expression.Expr × Expression.Expr × String × Bool) :=
  [("r@31749", .eq default (cst "n") (int 3), imp (op2 "Int.Lt" (int 2) (cst "n")) (.false default),
      "sat\n((n 3))\n", false),
   ("r@33869", .eq default (cst "n") (int 2), imp (op2 "Int.Le" (int 2) (cst "n")) (.false default),
      "sat\n((n 2))\n", false),
   ("r@34614", .eq default (cst "n") (int 1), imp (op2 "Int.Lt" (int 0) (cst "n")) (.false default),
      "sat\n((n 1))\n", false),
   ("r@42762", .eq default (cst "n") (int 2), imp (op2 "Int.Lt" (int 1) (cst "n")) (.false default),
      "sat\n((n 2))\n", false),
   ("r@43533", .eq default (int 2) (cst "n"), imp (op2 "Int.Lt" (int 1) (cst "n")) (.false default),
      "sat\n((n 2))\n", false),
   ("r@44314", .eq default (cst "n") (int 2), imp (op2 "Int.Lt" (int 1) (cst "n")) (.false default),
      "sat\n((n 2))\n", false),
   ("c@48887", .eq default (cst "n") (int 2), op2 "Int.Lt" (int 0) (cst "n"),
      "sat\n((n 2))\n", true)]

/--
info: r@31749: genuine (before: can't-validate: path condition did not reduce to a boolean)
r@33869: genuine (before: can't-validate: path condition did not reduce to a boolean)
r@34614: genuine (before: can't-validate: path condition did not reduce to a boolean)
r@42762: genuine (before: can't-validate: path condition did not reduce to a boolean)
r@43533: genuine (before: can't-validate: path condition did not reduce to a boolean)
r@44314: genuine (before: can't-validate: path condition did not reduce to a boolean)
c@48887: genuine (before: can't-validate: path condition did not reduce to a boolean)
-/
#guard_msgs in
#eval show IO Unit from do
  for (label, pc, goal, answer, cover) in ubqChecks do
    let o := obl label [.assumption "pc" pc] goal (if cover then .cover else .assert)
    IO.println s!"{label}: {← verdict nF o [] answer (cover := cover)} \
      (before: {← verdict nF o [] answer (interpret := false) (cover := cover)})"

/-! ## Corpus: `RealBitVector.lean`, `real_add_ge_bad`

`const x, y : real`. The constants take the model's values, but the factory's real
operators (`Real.Add`, `Real.Ge`) have no concrete evaluator, so the definition
`$__cse.0 := x + y` still does not reduce and the check cannot decide. -/

/-- `real_add_ge_bad`, cvc5's answer `x = 1.0, y = 2.0`. -/
private def realAddGeBad : IO String :=
  let r (d : Nat) : Expression.Expr := .rationalConst default d
  verdict (withDecls [("x", .real, []), ("y", .real, [])])
    (obl "real_add_ge_bad"
      [define "$__cse.0" .real (op2 "Real.Add" (cst "x") (cst "y")),
       define "$__cse.1" .bool (op2 "Real.Ge" (cst "y") (r 2)),
       define "$__cse.2" .bool (op2 "Real.Ge" (cst "x") (r 1)),
       .assumption "x" (fv "$__cse.2" .bool), .assumption "y" (fv "$__cse.1" .bool)]
      (op2 "Real.Ge" (fv "$__cse.0" .real) (r 4)))
    [] "sat\n((x 1.0) (y 2.0))\n"

/-- info: "can't-validate: varDecl RHS did not reduce" -/
#guard_msgs in
#eval realAddGeBad

/-! ## Parsing: a partial model and a rational value

In `partial`, one value of the answer is a function (`lambda`), which the parser cannot
read. `x` and `z` keep their values and the model validates (dropping the whole model
would leave the defaults `x = z = 0`, for which the goal holds). In `third`, z3 gives a
real the rational value `(/ 1.0 3.0)`. The model holds `1/3`, and the evaluator decides
the equality of real literals, so the model validates. -/

/-- info: "genuine" -/
#guard_msgs in
#eval verdict Core.Factory (obl "partial" [] (.eq default (fv "x" .int) (fv "z" .int)))
  [("x", .int), ("f", .int), ("z", .int)]
  "sat\n((x 1) (f (lambda ((_arg_1 Int)) 0)) (z 3))\n"

/-- info: "genuine" -/
#guard_msgs in
#eval verdict Core.Factory
  (obl "third" [] (.eq default (fv "x@1" .real) (.rationalConst default 0)))
  [("x@1", .real)] "sat\n((x@1 (/ 1.0 3.0)))\n"

/-! ## Guards: what must not validate

A constant with an axiom (`Func.axioms`) is not interpreted, because the check does not
evaluate that axiom. A constant that an assumption removed from the obligation mentions
is not interpreted, because the check does not see the removed assumption. Both stay
`cantValidate`. The controls are the same constant without the axiom, and the same
constant when the removed assumption mentions another one: both validate. -/

/-- `c > 10` with `c := 6`, where the factory constant `c` has the axioms `axioms` and
    `removed` were removed from the obligation. -/
private def guarded (axioms : List Expression.Expr)
    (removed : List (PathConditionEntry Expression)) : IO String :=
  verdict (withDecls [("c", .int, axioms)]) (obl "gt10" [] (op2 "Int.Gt" (cst "c") (int 10)))
    [] "sat\n((c 6))\n" (removed := removed)

/--
info: "can't-validate: goal did not reduce to a boolean"
"can't-validate: goal did not reduce to a boolean"
"genuine"
"genuine"
-/
#guard_msgs in
#eval show IO Unit from do
  let c5 := op2 "Int.Gt" (cst "c") (int 5)
  IO.println (repr (← guarded [c5] []))
  IO.println (repr (← guarded [] [.assumption "c5" c5]))
  IO.println (repr (← guarded [] []))
  IO.println (repr (← guarded [] [.assumption "d5" (op2 "Int.Gt" (cst "d") (int 5))]))

/-! ## The type gate

A model value that does not have its variable's type loses its `value?` flag
(`gateModelTypes`), so the check reads the variable's default instead. Here `x : int`
gets the value `true`. Gated, `x` reads `0`, for which the goal `x == 0` holds: the model
is not a counterexample (`spurious`). Without the gate the check reads `true`, and
`true == 0` compares values of two types: it does not type check, so the evaluator does not
evaluate it and the check cannot validate the model. The control, a well-typed `x = 1`,
validates. -/

/--
info: "spurious"
"can't-validate: goal did not reduce to a boolean"
"genuine"
-/
#guard_msgs in
#eval show IO Unit from do
  let o := obl "x1" [] (.eq default (fv "x" .int) (int 0))
  IO.println (repr (← verdict Core.Factory o [("x", .int)] "sat\n((x true))\n"))
  IO.println (repr (← verdict Core.Factory o [("x", .int)] "sat\n((x true))\n" (gate := false)))
  IO.println (repr (← verdict Core.Factory o [("x", .int)] "sat\n((x 1))\n"))

/-! ## Answers with `let` values and string escapes

13 real cvc5 answers from `lake build StrataTest StrataLaurelTest` (Laurel heaps and
strings), each with a value that has a `let` or a `\u{0}` string escape. A `let` is
substituted into its body, and the escaped string is decoded by the response dialect.
Each line shows how many of the requested variables the model keeps, and, as `before`,
how many a parser keeps that gives such a pair no value and drops the whole model when
one requested variable has no value. -/

/-- The variables requested by an answer: its keys, in order. -/
private def keysOf (resp : String) : List String :=
  (valuationPairStrings resp).map fun p => ((p.drop 1).takeWhile (· != ' ')).toString

/-- The number of requested variables a parser keeps that gives no value to a pair with
    a `let` (no `let` translation) or a `\u` string escape (no escape decoding) and drops
    the whole model when one value is missing: none when some value has a `let` or a
    `\u` escape, all of them otherwise. -/
private def keptBefore (resp : String) : Nat :=
  let lost := (valuationPairStrings resp).any fun p => p.contains "(let " || p.contains "\\u"
  if lost then 0 else (keysOf resp).length

/-- Print how many of the requested variables `processModel` finds in `resp`, and how
    many `keptBefore` counts. -/
private def kept (label resp : String) : IO Unit := do
  let keys := keysOf resp
  let vars : List Expression.TypedIdent := keys.map fun k => (⟨k, ()⟩, .forAll [] .int)
  match ← readAnswer vars ("sat\n" ++ resp) with
  | .ok (_, .sat m) =>
    IO.println s!"{label}: kept {m.length} of {keys.length} (before: {keptBefore resp})"
  | _ => IO.println s!"{label}: no model"

/-- The 13 answers, each labelled by its capture id. -/
private def lostAnswers : List (String × String) := [
  ("610870",
    "(($heap@11 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) (f.14 (store (store (store ((as const (Array TypeTag \
    Bool)) true) Base_TypeTag false) Base2_TypeTag false) Extender_TypeTag false)) (f.17 \
    (store ((as const (Array TypeTag Bool)) false) Top_TypeTag true)) (f.20 (store ((as \
    const (Array TypeTag Bool)) false) Base_TypeTag true)) (f.15 (store (store ((as const \
    (Array TypeTag Bool)) false) Top_TypeTag true) Right_TypeTag true)) (f.16 (store \
    (store ((as const (Array TypeTag Bool)) false) Top_TypeTag true) Left_TypeTag true)) \
    (a@3 (MkComposite 0 Base_TypeTag)) (f.18 (store (store (store ((as const (Array \
    TypeTag Bool)) false) Base_TypeTag true) Base2_TypeTag true) Extender_TypeTag true)) \
    ($heap@9 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) (f.21 (let ((_let_1 (store ((as const (Array TypeTag \
    Bool)) false) Top_TypeTag true))) (let ((_let_2 (store ((as const (Array TypeTag \
    Bool)) false) Base_TypeTag true))) (store (store (store (store (store (store ((as \
    const (Array TypeTag (Array TypeTag Bool))) _let_1) Base_TypeTag _let_2) \
    Base2_TypeTag (store ((as const (Array TypeTag Bool)) false) Base2_TypeTag true)) \
    Extender_TypeTag (store (store _let_2 Base2_TypeTag true) Extender_TypeTag true)) \
    Left_TypeTag (store _let_1 Left_TypeTag true)) Right_TypeTag (store _let_1 \
    Right_TypeTag true)) Bottom_TypeTag (store (store (store ((as const (Array TypeTag \
    Bool)) true) Base_TypeTag false) Base2_TypeTag false) Extender_TypeTag false))))) \
    (f.19 (store ((as const (Array TypeTag Bool)) false) Base2_TypeTag true)) ($heap@7 \
    (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) 0)))"),
  ("481474",
    "(($heap@8 (let ((_let_1 (MkComposite 0 Inner_TypeTag))) (MkHeap (store ((as const \
    (Array Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 1 \
    Inner_TypeTag))) Inner.a (BoxComposite _let_1))) (- 2)))) ($heap@10 (let ((_let_1 \
    (MkComposite (- 1) Inner_TypeTag))) (MkHeap (store (store (store ((as const (Array \
    Composite (Array Field $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) \
    Inner.a (BoxComposite (MkComposite 0 Inner_TypeTag)))) (MkComposite 0 Inner_TypeTag) \
    (store ((as const (Array Field $Box)) (BoxInt (- 1))) Inner.a (BoxInt 1))) \
    (MkComposite (- 2) Outer_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 1)) \
    Outer.inner (BoxComposite _let_1))) _let_1 (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 0 Outer_TypeTag))) Inner.a (BoxInt (- 1)))) 0))))"),
  ("369786",
    "(($heap@18 (let ((_let_1 (MkComposite 0 ticketLockReliesBadState_TypeTag))) (MkHeap \
    (store (store (store ((as const (Array Composite (Array Field $Box))) ((as const \
    (Array Field $Box)) (BoxInt 0))) (MkComposite 0 TLState_TypeTag) (store ((as const \
    (Array Field $Box)) (BoxInt 0)) TLState.nowServing (BoxInt (- 1)))) _let_1 (store \
    ((as const (Array Field $Box)) (BoxInt (- 1))) TLState.nowServing (BoxInt 0))) \
    (MkComposite 1 TLState_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 2)) \
    TLState.nowServing (BoxComposite _let_1))) 1))) ($cndtn_2 (MkHeap ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) \
    ($heap@20 (let ((_let_1 (MkComposite 0 ticketLockReliesBadState_TypeTag))) (MkHeap \
    (store (store (store ((as const (Array Composite (Array Field $Box))) ((as const \
    (Array Field $Box)) (BoxInt 0))) (MkComposite 0 TLState_TypeTag) (store ((as const \
    (Array Field $Box)) (BoxInt 0)) TLState.nowServing (BoxInt (- 1)))) _let_1 (store \
    ((as const (Array Field $Box)) (BoxInt (- 1))) TLState.nowServing (BoxInt 0))) \
    (MkComposite 1 TLState_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 2)) \
    TLState.nowServing (BoxComposite _let_1))) 0))) ($heap@21 (let ((_let_1 (MkComposite \
    0 TLState_TypeTag))) (MkHeap (store (store (store ((as const (Array Composite (Array \
    Field $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) TLState.nowServing \
    (BoxComposite _let_1))) _let_1 ((as const (Array Field $Box)) (BoxInt 1))) \
    (MkComposite 0 ticketLockReliesBadState_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite 0 ticketLockReliesBadState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_1))) (MkComposite 1 TLState_TypeTag) ((as const \
    (Array Field $Box)) (BoxComposite (MkComposite 1 TLState_TypeTag)))) 0))) (s@15 \
    (MkComposite 0 TLState_TypeTag)) ($cndtn_0 false) (myTicket@15 0) (s@14 (MkComposite \
    0 TLState_TypeTag)) ($heap@16 (MkHeap ((as const (Array Composite (Array Field \
    $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (myTicket@14 0) ($heap@22 \
    (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) 0)))"),
  ("374814",
    "(($heap@17 (let ((_let_1 (MkComposite 2 incBreaksEqualityState_TypeTag))) (let \
    ((_let_2 (MkComposite 2 Cell_TypeTag))) (let ((_let_3 (MkComposite 0 Cell_TypeTag))) \
    (MkHeap (store (store (store (store (store (store ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_3 (store ((as const \
    (Array Field $Box)) (BoxComposite (MkComposite 1 Cell_TypeTag))) Cell.x (BoxComposite \
    _let_3))) (MkComposite 0 incBreaksEqualityState_TypeTag) (store ((as const (Array \
    Field $Box)) (BoxComposite (MkComposite (- 1) incBreaksEqualityState_TypeTag))) \
    Cell.x (BoxInt (- 1)))) (MkComposite 1 Cell_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite (- 1) Cell_TypeTag))) Cell.x (BoxInt 2))) \
    (MkComposite 1 incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 1 incBreaksEqualityState_TypeTag))) Cell.x (BoxInt (- \
    2)))) _let_2 (store ((as const (Array Field $Box)) (BoxInt 4)) Cell.x (BoxComposite \
    _let_2))) _let_1 (store ((as const (Array Field $Box)) (BoxInt (- 4))) Cell.x \
    (BoxComposite _let_1))) 0))))) ($old_heap@4 (let ((_let_1 (MkComposite 2 \
    incBreaksEqualityState_TypeTag))) (let ((_let_2 (MkComposite 2 Cell_TypeTag))) (let \
    ((_let_3 (MkComposite 0 Cell_TypeTag))) (MkHeap (store (store (store (store (store \
    (store ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) _let_3 (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite 1 Cell_TypeTag))) Cell.x (BoxComposite _let_3))) (MkComposite 0 \
    incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite (- 1) incBreaksEqualityState_TypeTag))) Cell.x (BoxInt (- 1)))) \
    (MkComposite 1 Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite (- 1) Cell_TypeTag))) Cell.x (BoxInt 2))) (MkComposite 1 \
    incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite 1 incBreaksEqualityState_TypeTag))) Cell.x (BoxInt (- 2)))) _let_2 \
    (store ((as const (Array Field $Box)) (BoxInt 4)) Cell.x (BoxComposite _let_2))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxInt (- 4))) Cell.x (BoxComposite \
    _let_1))) (- 2)))))) ($cndtn_2 (MkHeap ((as const (Array Composite (Array Field \
    $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) ($heap@20 (let ((_let_1 \
    (MkComposite 2 incBreaksEqualityState_TypeTag))) (let ((_let_2 (MkComposite 2 \
    Cell_TypeTag))) (let ((_let_3 (MkComposite 0 Cell_TypeTag))) (MkHeap (store (store \
    (store (store (store (store ((as const (Array Composite (Array Field $Box))) ((as \
    const (Array Field $Box)) (BoxInt 0))) _let_3 (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 1 Cell_TypeTag))) Cell.x (BoxComposite _let_3))) \
    (MkComposite 0 incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite (- 1) incBreaksEqualityState_TypeTag))) Cell.x (BoxInt (- \
    1)))) (MkComposite 1 Cell_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite (- 1) Cell_TypeTag))) Cell.x (BoxInt 2))) (MkComposite 1 \
    incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite 1 incBreaksEqualityState_TypeTag))) Cell.x (BoxInt (- 2)))) _let_2 \
    (store ((as const (Array Field $Box)) (BoxInt 4)) Cell.x (BoxComposite _let_2))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxInt (- 4))) Cell.x (BoxComposite \
    _let_1))) 0))))) ($heap@21 (let ((_let_1 (MkComposite 0 \
    incBreaksEqualityState_TypeTag))) (MkHeap (store (store (store (store (store ((as \
    const (Array Composite (Array Field $Box))) (store ((as const (Array Field $Box)) \
    (BoxInt 0)) Cell.x (BoxComposite (MkComposite 0 Cell_TypeTag)))) (MkComposite 0 \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt (- 1))) Cell.x \
    (BoxComposite _let_1))) _let_1 (store ((as const (Array Field $Box)) (BoxInt 3)) \
    Cell.x (BoxComposite (MkComposite 1 Cell_TypeTag)))) (MkComposite (- 1) Cell_TypeTag) \
    ((as const (Array Field $Box)) (BoxInt 1))) (MkComposite (- 1) \
    incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite 2 Cell_TypeTag))) Cell.x (BoxInt 3))) (MkComposite 2 Cell_TypeTag) \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 2 \
    incBreaksEqualityState_TypeTag))) Cell.x (BoxInt (- 3)))) 0))) ($heap@23 (let \
    ((_let_1 (MkComposite (- 1) incBreaksEqualityState_TypeTag))) (let ((_let_2 \
    (MkComposite (- 1) Cell_TypeTag))) (let ((_let_3 (MkComposite 1 \
    incBreaksEqualityState_TypeTag))) (MkHeap (store (store (store (store (store ((as \
    const (Array Composite (Array Field $Box))) (store ((as const (Array Field $Box)) \
    (BoxInt 0)) Cell.x (BoxInt 1))) (MkComposite 1 Cell_TypeTag) (store ((as const (Array \
    Field $Box)) (BoxInt (- 2))) Cell.x (BoxComposite _let_3))) _let_3 (store ((as const \
    (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite _let_2))) _let_2 (store ((as \
    const (Array Field $Box)) (BoxComposite (MkComposite 0 \
    incBreaksEqualityState_TypeTag))) Cell.x (BoxInt 10))) _let_1 (store ((as const \
    (Array Field $Box)) (BoxInt (- 3))) Cell.x (BoxComposite _let_1))) (MkComposite 2 \
    incBreaksEqualityState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite (- 2) Cell_TypeTag))) Cell.x (BoxInt 4))) 2))))) (s@13 (MkComposite 0 \
    Cell_TypeTag)) ($cndtn_0 false) ($heap@15 (MkHeap ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (s@14 (MkComposite (- \
    1) Cell_TypeTag)) ($cndtn_1 (MkHeap ((as const (Array Composite (Array Field $Box))) \
    ((as const (Array Field $Box)) (BoxInt 0))) 0)))"),
  ("217029",
    "(($heap@18 (let ((_let_1 (MkComposite (- 2) TLState_TypeTag))) (let ((_let_2 \
    (MkComposite 2 ticketLockReliesBadState_TypeTag))) (let ((_let_3 (MkComposite (- 1) \
    ticketLockReliesBadState_TypeTag))) (let ((_let_4 (MkComposite (- 1) \
    TLState_TypeTag))) (let ((_let_5 (MkComposite 1 ticketLockReliesBadState_TypeTag))) \
    (let ((_let_6 (MkComposite 1 TLState_TypeTag))) (let ((_let_7 (MkComposite 0 \
    TLState_TypeTag))) (MkHeap (store (store (store (store (store (store (store (store \
    (store ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) _let_7 (store ((as const (Array Field $Box)) (BoxInt 0)) \
    TLState.nowServing (BoxInt (- 1)))) (MkComposite 0 ticketLockReliesBadState_TypeTag) \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 3 \
    ticketLockReliesBadState_TypeTag))) TLState.nowServing (BoxComposite _let_7))) _let_6 \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 3 TLState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_6))) _let_5 (store ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite (- 2) ticketLockReliesBadState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_5))) _let_4 (store ((as const (Array Field \
    $Box)) (BoxComposite _let_1)) TLState.nowServing (BoxComposite _let_4))) _let_3 \
    (store ((as const (Array Field $Box)) (BoxComposite _let_2)) TLState.nowServing \
    (BoxComposite _let_3))) (MkComposite 2 TLState_TypeTag) ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite 2 TLState_TypeTag)))) _let_2 (store ((as const \
    (Array Field $Box)) (BoxComposite _let_3)) TLState.nowServing (BoxComposite _let_2))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxComposite _let_4)) \
    TLState.nowServing (BoxComposite _let_1))) 1))))))))) ($old_heap@4 (MkHeap (store \
    (store (store (store (store (store ((as const (Array Composite (Array Field $Box))) \
    (store ((as const (Array Field $Box)) (BoxInt 0)) TLState.nowServing (BoxInt 1))) \
    (MkComposite 0 TLState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite 0 ticketLockReliesBadState_TypeTag))) TLState.nowServing (BoxInt 1))) \
    (MkComposite 1 ticketLockReliesBadState_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 5)) TLState.nowServing (BoxInt (- 2)))) (MkComposite 2 \
    ticketLockReliesBadState_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 3)) \
    TLState.nowServing (BoxInt (- 4)))) (MkComposite (- 2) TLState_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxInt (- 2))) TLState.nowServing (BoxInt 5))) \
    (MkComposite (- 2) ticketLockReliesBadState_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 2)) TLState.nowServing (BoxInt (- 5)))) (MkComposite 3 \
    TLState_TypeTag) (store ((as const (Array Field $Box)) (BoxInt (- 1))) \
    TLState.nowServing (BoxInt 6))) (- 2))) ($cndtn_2 (MkHeap ((as const (Array Composite \
    (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) ($heap@20 (let \
    ((_let_1 (MkComposite (- 2) TLState_TypeTag))) (let ((_let_2 (MkComposite 2 \
    ticketLockReliesBadState_TypeTag))) (let ((_let_3 (MkComposite (- 1) \
    ticketLockReliesBadState_TypeTag))) (let ((_let_4 (MkComposite (- 1) \
    TLState_TypeTag))) (let ((_let_5 (MkComposite 1 ticketLockReliesBadState_TypeTag))) \
    (let ((_let_6 (MkComposite 1 TLState_TypeTag))) (let ((_let_7 (MkComposite 0 \
    TLState_TypeTag))) (MkHeap (store (store (store (store (store (store (store (store \
    (store ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) _let_7 (store ((as const (Array Field $Box)) (BoxInt 0)) \
    TLState.nowServing (BoxInt (- 1)))) (MkComposite 0 ticketLockReliesBadState_TypeTag) \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 3 \
    ticketLockReliesBadState_TypeTag))) TLState.nowServing (BoxComposite _let_7))) _let_6 \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 3 TLState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_6))) _let_5 (store ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite (- 2) ticketLockReliesBadState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_5))) _let_4 (store ((as const (Array Field \
    $Box)) (BoxComposite _let_1)) TLState.nowServing (BoxComposite _let_4))) _let_3 \
    (store ((as const (Array Field $Box)) (BoxComposite _let_2)) TLState.nowServing \
    (BoxComposite _let_3))) (MkComposite 2 TLState_TypeTag) ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite 2 TLState_TypeTag)))) _let_2 (store ((as const \
    (Array Field $Box)) (BoxComposite _let_3)) TLState.nowServing (BoxComposite _let_2))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxComposite _let_4)) \
    TLState.nowServing (BoxComposite _let_1))) 0))))))))) ($heap@21 (let ((_let_1 \
    (MkComposite (- 2) TLState_TypeTag))) (let ((_let_2 (MkComposite 2 \
    ticketLockReliesBadState_TypeTag))) (let ((_let_3 (MkComposite (- 1) \
    ticketLockReliesBadState_TypeTag))) (let ((_let_4 (MkComposite (- 1) \
    TLState_TypeTag))) (let ((_let_5 (MkComposite 1 ticketLockReliesBadState_TypeTag))) \
    (let ((_let_6 (MkComposite 1 TLState_TypeTag))) (let ((_let_7 (MkComposite 0 \
    TLState_TypeTag))) (MkHeap (store (store (store (store (store (store (store (store \
    (store ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) _let_7 (store ((as const (Array Field $Box)) (BoxInt 0)) \
    TLState.nowServing (BoxInt (- 1)))) (MkComposite 0 ticketLockReliesBadState_TypeTag) \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 3 \
    ticketLockReliesBadState_TypeTag))) TLState.nowServing (BoxComposite _let_7))) _let_6 \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 3 TLState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_6))) _let_5 (store ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite (- 2) ticketLockReliesBadState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_5))) _let_4 (store ((as const (Array Field \
    $Box)) (BoxComposite _let_1)) TLState.nowServing (BoxComposite _let_4))) _let_3 \
    (store ((as const (Array Field $Box)) (BoxComposite _let_2)) TLState.nowServing \
    (BoxComposite _let_3))) (MkComposite 2 TLState_TypeTag) ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite 2 TLState_TypeTag)))) _let_2 (store ((as const \
    (Array Field $Box)) (BoxComposite _let_3)) TLState.nowServing (BoxComposite _let_2))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxComposite _let_4)) \
    TLState.nowServing (BoxComposite _let_1))) 0))))))))) (s@15 (MkComposite 0 \
    TLState_TypeTag)) ($cndtn_0 false) (myTicket@15 0) (s@14 (MkComposite 0 \
    TLState_TypeTag)) ($heap@16 (MkHeap ((as const (Array Composite (Array Field $Box))) \
    ((as const (Array Field $Box)) (BoxInt 0))) 0)) (myTicket@14 0) ($heap@22 (let \
    ((_let_1 (MkComposite 3 TLState_TypeTag))) (let ((_let_2 (MkComposite (- 2) \
    ticketLockReliesBadState_TypeTag))) (let ((_let_3 (MkComposite 0 \
    ticketLockReliesBadState_TypeTag))) (MkHeap (store (store (store (store (store (store \
    (store (store ((as const (Array Composite (Array Field $Box))) (store ((as const \
    (Array Field $Box)) (BoxInt 0)) TLState.nowServing (BoxComposite (MkComposite 0 \
    TLState_TypeTag)))) (MkComposite 0 TLState_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 1)) TLState.nowServing (BoxInt 0))) _let_3 (store ((as const (Array \
    Field $Box)) (BoxInt 6)) TLState.nowServing (BoxComposite _let_3))) (MkComposite 1 \
    TLState_TypeTag) (store ((as const (Array Field $Box)) (BoxInt (- 5))) \
    TLState.nowServing (BoxInt 2))) (MkComposite (- 1) TLState_TypeTag) (store ((as const \
    (Array Field $Box)) (BoxInt (- 4))) TLState.nowServing (BoxInt 3))) (MkComposite (- \
    1) ticketLockReliesBadState_TypeTag) (store ((as const (Array Field $Box)) (BoxInt \
    4)) TLState.nowServing (BoxInt (- 3)))) (MkComposite 2 TLState_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxInt (- 3))) TLState.nowServing (BoxInt 4))) _let_2 \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 1 \
    ticketLockReliesBadState_TypeTag))) TLState.nowServing (BoxComposite _let_2))) _let_1 \
    (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 1 TLState_TypeTag))) \
    TLState.nowServing (BoxComposite _let_1))) 2))))) ($cndtn_1 (MkHeap ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)))"),
  ("834557",
    "(($old_heap@2 (MkHeap (store (store (store ((as const (Array Composite (Array Field \
    $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxComposite \
    (MkComposite 0 Cell_TypeTag)))) (MkComposite 0 Cell_TypeTag) (store ((as const (Array \
    Field $Box)) (BoxComposite (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag))) Cell.x (BoxInt 1))) (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 1 Cell_TypeTag))) Cell.x (BoxInt (- 1)))) (MkComposite (- \
    1) Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxInt \
    2))) (- 2))) ($heap@17 (let ((_let_1 (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_2 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store (store ((as const (Array Composite (Array Field \
    $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_2 (store ((as const (Array \
    Field $Box)) (BoxInt (- 1))) Cell.x (BoxComposite _let_2))) _let_1 (store ((as const \
    (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite _let_1))) (MkComposite (- 1) \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 1)) Cell.x (BoxInt 0))) \
    0)))) ($heap@20 (let ((_let_1 (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_2 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store (store ((as const (Array Composite (Array Field \
    $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_2 (store ((as const (Array \
    Field $Box)) (BoxInt (- 1))) Cell.x (BoxComposite _let_2))) _let_1 (store ((as const \
    (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite _let_1))) (MkComposite (- 1) \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 1)) Cell.x (BoxInt 0))) \
    1)))) ($heap@21 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const \
    (Array Field $Box)) (BoxInt 0))) 0)) ($heap@23 (MkHeap ((as const (Array Composite \
    (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (s@13 \
    (MkComposite 0 Cell_TypeTag)) ($cndtn_0 false) ($heap@15 (MkHeap ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (s@14 \
    (MkComposite (- 1) Cell_TypeTag)) ($cndtn_1 (MkHeap ((as const (Array Composite \
    (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)))"),
  ("334253",
    "(($heap@17 (let ((_let_1 (MkComposite (- 1) \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_2 (MkComposite (- 1) \
    Cell_TypeTag))) (let ((_let_3 (MkComposite 1 \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_4 (MkComposite 1 \
    Cell_TypeTag))) (let ((_let_5 (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_6 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store (store (store (store (store (store ((as const \
    (Array Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) \
    _let_6 (store ((as const (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite \
    _let_6))) _let_5 (store ((as const (Array Field $Box)) (BoxInt (- 2))) Cell.x \
    (BoxComposite _let_5))) _let_4 (store ((as const (Array Field $Box)) (BoxInt 3)) \
    Cell.x (BoxComposite _let_4))) _let_3 (store ((as const (Array Field $Box)) (BoxInt \
    (- 3))) Cell.x (BoxComposite _let_3))) _let_2 (store ((as const (Array Field $Box)) \
    (BoxInt (- 1))) Cell.x (BoxInt 0))) _let_1 (store ((as const (Array Field $Box)) \
    (BoxInt 4)) Cell.x (BoxComposite _let_2))) (MkComposite 2 Cell_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxInt (- 4))) Cell.x (BoxComposite _let_1))) 0)))))))) \
    ($old_heap@4 (MkHeap (store (store (store (store (store ((as const (Array Composite \
    (Array Field $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxInt \
    1))) (MkComposite (- 1) Cell_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 0 incMonotonicMissingInvariantState_TypeTag))) Cell.x \
    (BoxInt 11))) (MkComposite (- 1) incMonotonicMissingInvariantState_TypeTag) (store \
    ((as const (Array Field $Box)) (BoxComposite (MkComposite 2 Cell_TypeTag))) Cell.x \
    (BoxInt 3))) (MkComposite 2 Cell_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 2 incMonotonicMissingInvariantState_TypeTag))) Cell.x \
    (BoxInt (- 3)))) (MkComposite 2 incMonotonicMissingInvariantState_TypeTag) (store \
    ((as const (Array Field $Box)) (BoxComposite (MkComposite (- 2) Cell_TypeTag))) \
    Cell.x (BoxInt 4))) (MkComposite (- 2) Cell_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxComposite (MkComposite (- 2) incMonotonicMissingInvariantState_TypeTag))) \
    Cell.x (BoxInt (- 4)))) 2)) ($cndtn_2 (MkHeap ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) ($heap@20 (let ((_let_1 \
    (MkComposite (- 1) incMonotonicMissingInvariantState_TypeTag))) (let ((_let_2 \
    (MkComposite (- 1) Cell_TypeTag))) (let ((_let_3 (MkComposite 1 \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_4 (MkComposite 1 \
    Cell_TypeTag))) (let ((_let_5 (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag))) (let ((_let_6 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store (store (store (store (store (store ((as const \
    (Array Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) \
    _let_6 (store ((as const (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite \
    _let_6))) _let_5 (store ((as const (Array Field $Box)) (BoxInt (- 2))) Cell.x \
    (BoxComposite _let_5))) _let_4 (store ((as const (Array Field $Box)) (BoxInt 3)) \
    Cell.x (BoxComposite _let_4))) _let_3 (store ((as const (Array Field $Box)) (BoxInt \
    (- 3))) Cell.x (BoxComposite _let_3))) _let_2 (store ((as const (Array Field $Box)) \
    (BoxInt (- 1))) Cell.x (BoxInt 0))) _let_1 (store ((as const (Array Field $Box)) \
    (BoxInt 4)) Cell.x (BoxComposite _let_2))) (MkComposite 2 Cell_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxInt (- 4))) Cell.x (BoxComposite _let_1))) 0)))))))) \
    ($heap@21 (let ((_let_1 (MkComposite 2 incMonotonicMissingInvariantState_TypeTag))) \
    (MkHeap (store (store (store (store (store (store (store ((as const (Array Composite \
    (Array Field $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x \
    (BoxComposite (MkComposite 0 Cell_TypeTag)))) (MkComposite 0 Cell_TypeTag) (store \
    ((as const (Array Field $Box)) (BoxComposite (MkComposite 1 Cell_TypeTag))) Cell.x \
    (BoxInt 1))) (MkComposite 0 incMonotonicMissingInvariantState_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxComposite (MkComposite 1 \
    incMonotonicMissingInvariantState_TypeTag))) Cell.x (BoxInt (- 1)))) (MkComposite 1 \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite (MkComposite (- 1) \
    Cell_TypeTag))) Cell.x (BoxInt 2))) (MkComposite 1 \
    incMonotonicMissingInvariantState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite (- 1) incMonotonicMissingInvariantState_TypeTag))) Cell.x \
    (BoxInt (- 2)))) (MkComposite (- 1) Cell_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 0)) Cell.x (BoxInt 10))) _let_1 (store ((as const (Array Field $Box)) \
    (BoxInt 5)) Cell.x (BoxComposite (MkComposite 2 Cell_TypeTag)))) (MkComposite (- 2) \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt (- 5))) Cell.x \
    (BoxComposite _let_1))) 0))) ($heap@23 (let ((_let_1 (MkComposite 2 \
    incMonotonicMissingInvariantState_TypeTag))) (MkHeap (store (store (store (store \
    (store (store (store ((as const (Array Composite (Array Field $Box))) (store ((as \
    const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxComposite (MkComposite 0 \
    Cell_TypeTag)))) (MkComposite 0 Cell_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 1 Cell_TypeTag))) Cell.x (BoxInt 1))) (MkComposite 0 \
    incMonotonicMissingInvariantState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 1 incMonotonicMissingInvariantState_TypeTag))) Cell.x \
    (BoxInt (- 1)))) (MkComposite 1 Cell_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite (- 1) Cell_TypeTag))) Cell.x (BoxInt 2))) (MkComposite 1 \
    incMonotonicMissingInvariantState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite (- 1) incMonotonicMissingInvariantState_TypeTag))) Cell.x \
    (BoxInt (- 2)))) (MkComposite (- 1) Cell_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 0)) Cell.x (BoxInt 10))) _let_1 (store ((as const (Array Field $Box)) \
    (BoxInt 5)) Cell.x (BoxComposite (MkComposite 2 Cell_TypeTag)))) (MkComposite (- 2) \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt (- 5))) Cell.x \
    (BoxComposite _let_1))) 1))) (s@13 (MkComposite 0 Cell_TypeTag)) ($cndtn_0 false) \
    ($heap@15 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) (s@14 (MkComposite (- 1) Cell_TypeTag)) ($cndtn_1 \
    (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) 0)))"),
  ("862724",
    "(($heap@18 (MkHeap (store (store ((as const (Array Composite (Array Field $Box))) \
    (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxComposite (MkComposite 0 \
    Cell_TypeTag)))) (MkComposite 0 Cell_TypeTag) ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite 0 noopState_TypeTag)))) (MkComposite (- 1) Cell_TypeTag) \
    (store (store ((as const (Array Field $Box)) (BoxInt 1)) Cell.x (BoxInt 0)) \
    noopState.s (BoxInt 2))) 0)) ($heap@14 (MkHeap ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) ($g_tmp0@1 (MkComposite \
    (- 1) Cell_TypeTag)) ($heap@20 (MkHeap (store (store ((as const (Array Composite \
    (Array Field $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x \
    (BoxComposite (MkComposite 0 Cell_TypeTag)))) (MkComposite 0 Cell_TypeTag) ((as const \
    (Array Field $Box)) (BoxComposite (MkComposite 0 noopState_TypeTag)))) (MkComposite \
    (- 1) Cell_TypeTag) (store (store ((as const (Array Field $Box)) (BoxInt 1)) Cell.x \
    (BoxInt 0)) noopState.s (BoxInt 2))) 0)) ($heap@21 (let ((_let_1 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store ((as const (Array Composite (Array Field \
    $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_1 (store ((as const (Array \
    Field $Box)) (BoxInt (- 1))) Cell.x (BoxComposite _let_1))) (MkComposite (- 1) \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxInt 1))) \
    0))) (s@15 (MkComposite 0 Cell_TypeTag)) ($heap@24 (MkHeap ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (s@12 \
    (MkComposite 0 Cell_TypeTag)) (s@14 (MkComposite (- 1) Cell_TypeTag)) ($heap@22 \
    (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) 0)))"),
  ("549406",
    "(($heap@17 (let ((_let_1 (MkComposite 1 Cell_TypeTag))) (let ((_let_2 (MkComposite 0 \
    decBreaksMonotonicState_TypeTag))) (let ((_let_3 (MkComposite 0 Cell_TypeTag))) \
    (MkHeap (store (store (store (store (store ((as const (Array Composite (Array Field \
    $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_3 (store ((as const (Array \
    Field $Box)) (BoxInt (- 1))) Cell.x (BoxComposite _let_3))) _let_2 (store ((as const \
    (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite _let_2))) _let_1 (store ((as \
    const (Array Field $Box)) (BoxInt (- 2))) Cell.x (BoxComposite _let_1))) (MkComposite \
    1 decBreaksMonotonicState_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxComposite (MkComposite (- 1) Cell_TypeTag))) Cell.x (BoxInt (- 2)))) (MkComposite \
    (- 1) Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxInt \
    10))) 0))))) ($old_heap@4 (let ((_let_1 (MkComposite 1 Cell_TypeTag))) (let ((_let_2 \
    (MkComposite 0 decBreaksMonotonicState_TypeTag))) (let ((_let_3 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store (store (store (store ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_3 \
    (store ((as const (Array Field $Box)) (BoxInt (- 1))) Cell.x (BoxComposite _let_3))) \
    _let_2 (store ((as const (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite \
    _let_2))) _let_1 (store ((as const (Array Field $Box)) (BoxInt (- 2))) Cell.x \
    (BoxComposite _let_1))) (MkComposite 1 decBreaksMonotonicState_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxComposite (MkComposite (- 1) Cell_TypeTag))) Cell.x \
    (BoxInt (- 2)))) (MkComposite (- 1) Cell_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 0)) Cell.x (BoxInt 10))) 2))))) ($heap@20 (let ((_let_1 (MkComposite 1 \
    Cell_TypeTag))) (let ((_let_2 (MkComposite 0 decBreaksMonotonicState_TypeTag))) (let \
    ((_let_3 (MkComposite 0 Cell_TypeTag))) (MkHeap (store (store (store (store (store \
    ((as const (Array Composite (Array Field $Box))) ((as const (Array Field $Box)) \
    (BoxInt 0))) _let_3 (store ((as const (Array Field $Box)) (BoxInt (- 1))) Cell.x \
    (BoxComposite _let_3))) _let_2 (store ((as const (Array Field $Box)) (BoxInt 2)) \
    Cell.x (BoxComposite _let_2))) _let_1 (store ((as const (Array Field $Box)) (BoxInt \
    (- 2))) Cell.x (BoxComposite _let_1))) (MkComposite 1 \
    decBreaksMonotonicState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite (- 1) Cell_TypeTag))) Cell.x (BoxInt (- 2)))) (MkComposite (- 1) \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.x (BoxInt 10))) \
    0))))) ($heap@21 (let ((_let_1 (MkComposite 1 Cell_TypeTag))) (let ((_let_2 \
    (MkComposite 0 decBreaksMonotonicState_TypeTag))) (let ((_let_3 (MkComposite 0 \
    Cell_TypeTag))) (MkHeap (store (store (store (store (store ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) _let_3 \
    (store ((as const (Array Field $Box)) (BoxInt (- 1))) Cell.x (BoxComposite _let_3))) \
    _let_2 (store ((as const (Array Field $Box)) (BoxInt 2)) Cell.x (BoxComposite \
    _let_2))) _let_1 (store ((as const (Array Field $Box)) (BoxInt (- 2))) Cell.x \
    (BoxComposite _let_1))) (MkComposite 1 decBreaksMonotonicState_TypeTag) (store ((as \
    const (Array Field $Box)) (BoxComposite (MkComposite (- 1) Cell_TypeTag))) Cell.x \
    (BoxInt (- 2)))) (MkComposite (- 1) Cell_TypeTag) (store ((as const (Array Field \
    $Box)) (BoxInt 0)) Cell.x (BoxInt 10))) 0))))) ($heap@23 (let ((_let_1 (MkComposite 1 \
    decBreaksMonotonicState_TypeTag))) (MkHeap (store (store (store (store (store ((as \
    const (Array Composite (Array Field $Box))) (store ((as const (Array Field $Box)) \
    (BoxInt 0)) Cell.x (BoxComposite (MkComposite 0 Cell_TypeTag)))) (MkComposite 0 \
    Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite (MkComposite 0 \
    decBreaksMonotonicState_TypeTag))) Cell.x (BoxInt 1))) (MkComposite 0 \
    decBreaksMonotonicState_TypeTag) (store ((as const (Array Field $Box)) (BoxComposite \
    (MkComposite 1 Cell_TypeTag))) Cell.x (BoxInt (- 1)))) (MkComposite 1 Cell_TypeTag) \
    (store ((as const (Array Field $Box)) (BoxComposite _let_1)) Cell.x (BoxInt 2))) \
    _let_1 (store ((as const (Array Field $Box)) (BoxInt 3)) Cell.x (BoxComposite \
    _let_1))) (MkComposite (- 1) Cell_TypeTag) (store ((as const (Array Field $Box)) \
    (BoxInt 1)) Cell.x (BoxInt 0))) 1))) (s@13 (MkComposite 0 Cell_TypeTag)) ($heap@15 \
    (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) 0)) (s@14 (MkComposite (- 1) Cell_TypeTag)))"),
  ("332749",
    "((b@1 \"\\u{0}\") (a@1 \"\"))"),
  ("263064",
    "((self@4 (MkComposite 0 Box$a1$int_TypeTag)) ($heap@4 (MkHeap ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) Mk$Box)) 0)) (f.9 \
    (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$0_TypeTag true) SBox$a1$$Witness$SBox$get$0_TypeTag true)) \
    (f.16 (store ((as const (Array TypeTag Bool)) false) Box$a1$int_TypeTag true)) (r@6 \
    7) (f.11 (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true) \
    SBox$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true)) (f.13 (store (store ((as \
    const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true) \
    SBox$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true)) (f.17 (let ((_let_1 \
    (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true))) (let ((_let_2 (store ((as \
    const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true))) (let ((_let_3 (store ((as \
    const (Array TypeTag Bool)) false) Box$a1$int_TypeTag true))) (store (store (store \
    (store (store (store (store (store (store (store ((as const (Array TypeTag (Array \
    TypeTag Bool))) (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$0_TypeTag true)) Box$a1$int_TypeTag _let_3) \
    SBox$a1$int_TypeTag (store _let_3 SBox$a1$int_TypeTag true)) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag _let_2) \
    SBox$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag (store _let_2 \
    SBox$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true)) \
    Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag _let_1) \
    SBox$a1$$Witness$SBox$get$Box$childspec$0_TypeTag (store _let_1 \
    SBox$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true)) \
    SBox$a1$$Witness$SBox$get$0_TypeTag (store (store ((as const (Array TypeTag Bool)) \
    false) Box$a1$$Witness$SBox$get$0_TypeTag true) SBox$a1$$Witness$SBox$get$0_TypeTag \
    true)) $Witness$SBox$get$Box$refines$post$0_TypeTag (store ((as const (Array TypeTag \
    Bool)) false) $Witness$SBox$get$Box$refines$post$0_TypeTag true)) \
    $Witness$SBox$get$Box$childspec$0_TypeTag (store ((as const (Array TypeTag Bool)) \
    false) $Witness$SBox$get$Box$childspec$0_TypeTag true)) $Witness$SBox$get$0_TypeTag \
    (store ((as const (Array TypeTag Bool)) false) $Witness$SBox$get$0_TypeTag true)))))) \
    (f.7 (store ((as const (Array TypeTag Bool)) false) \
    $Witness$SBox$get$Box$childspec$0_TypeTag true)) (f.10 (store ((as const (Array \
    TypeTag Bool)) false) Box$a1$$Witness$SBox$get$0_TypeTag true)) (f.12 (store ((as \
    const (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag \
    true)) (f.8 (store ((as const (Array TypeTag Bool)) false) \
    $Witness$SBox$get$Box$refines$post$0_TypeTag true)) (f.15 (store (store ((as const \
    (Array TypeTag Bool)) false) Box$a1$int_TypeTag true) SBox$a1$int_TypeTag true)) (f.6 \
    (store ((as const (Array TypeTag Bool)) false) $Witness$SBox$get$0_TypeTag true)) \
    (f.14 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true)) (r@4 0))"),
  ("651595",
    "((f.7 (store ((as const (Array TypeTag Bool)) false) $Witness$SBox$get$impl$0_TypeTag \
    true)) (f.12 (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$0_TypeTag true) SBox$a1$$Witness$SBox$get$0_TypeTag true)) \
    (f.17 (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$Box$get$0_TypeTag true) SBox$a1$$Witness$Box$get$0_TypeTag true)) \
    (f.15 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$impl$0_TypeTag true)) (f.9 (store ((as const (Array TypeTag \
    Bool)) false) $Witness$Box$get$0_TypeTag true)) (f.14 (store (store ((as const (Array \
    TypeTag Bool)) false) Box$a1$$Witness$SBox$get$impl$0_TypeTag true) \
    SBox$a1$$Witness$SBox$get$impl$0_TypeTag true)) (self@3 (MkComposite 0 \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag)) (r@8 0) (f.19 (store (store \
    ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true) \
    SBox$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true)) (r@3 (- 5)) (f.16 (store \
    ((as const (Array TypeTag Bool)) false) Box$a1$$Witness$Box$get$impl$0_TypeTag true)) \
    (f.21 (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true) \
    SBox$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true)) (f.23 (let ((_let_1 \
    (store ((as const (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$get$0_TypeTag \
    true))) (let ((_let_2 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$impl$0_TypeTag true))) (let ((_let_3 (store ((as const \
    (Array TypeTag Bool)) false) Box$a1$$Witness$Box$get$0_TypeTag true))) (let ((_let_4 \
    (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true))) (let ((_let_5 (store ((as \
    const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true))) (store (store (store \
    (store (store (store (store (store (store (store (store (store (store (store (store \
    (store ((as const (Array TypeTag (Array TypeTag Bool))) (store ((as const (Array \
    TypeTag Bool)) false) $Witness$SBox$get$impl$0_TypeTag true)) \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag _let_5) \
    SBox$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag (store _let_5 \
    SBox$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag true)) \
    Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag _let_4) \
    SBox$a1$$Witness$SBox$get$Box$childspec$0_TypeTag (store _let_4 \
    SBox$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true)) \
    Box$a1$$Witness$Box$get$0_TypeTag _let_3) SBox$a1$$Witness$Box$get$0_TypeTag (store \
    _let_3 SBox$a1$$Witness$Box$get$0_TypeTag true)) \
    Box$a1$$Witness$Box$get$impl$0_TypeTag (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$Box$get$impl$0_TypeTag true)) Box$a1$$Witness$SBox$get$impl$0_TypeTag \
    _let_2) SBox$a1$$Witness$SBox$get$impl$0_TypeTag (store _let_2 \
    SBox$a1$$Witness$SBox$get$impl$0_TypeTag true)) Box$a1$$Witness$SBox$get$0_TypeTag \
    _let_1) SBox$a1$$Witness$SBox$get$0_TypeTag (store _let_1 \
    SBox$a1$$Witness$SBox$get$0_TypeTag true)) \
    $Witness$SBox$get$Box$refines$post$0_TypeTag (store ((as const (Array TypeTag Bool)) \
    false) $Witness$SBox$get$Box$refines$post$0_TypeTag true)) \
    $Witness$SBox$get$Box$childspec$0_TypeTag (store ((as const (Array TypeTag Bool)) \
    false) $Witness$SBox$get$Box$childspec$0_TypeTag true)) $Witness$Box$get$0_TypeTag \
    (store ((as const (Array TypeTag Bool)) false) $Witness$Box$get$0_TypeTag true)) \
    $Witness$Box$get$impl$0_TypeTag (store ((as const (Array TypeTag Bool)) false) \
    $Witness$Box$get$impl$0_TypeTag true)) $Witness$SBox$get$0_TypeTag (store ((as const \
    (Array TypeTag Bool)) false) $Witness$SBox$get$0_TypeTag true)))))))) (f.18 (store \
    ((as const (Array TypeTag Bool)) false) Box$a1$$Witness$Box$get$0_TypeTag true)) \
    (f.10 (store ((as const (Array TypeTag Bool)) false) \
    $Witness$SBox$get$Box$childspec$0_TypeTag true)) (f.13 (store ((as const (Array \
    TypeTag Bool)) false) Box$a1$$Witness$SBox$get$0_TypeTag true)) (f.11 (store ((as \
    const (Array TypeTag Bool)) false) $Witness$SBox$get$Box$refines$post$0_TypeTag \
    true)) (f.8 (store ((as const (Array TypeTag Bool)) false) \
    $Witness$Box$get$impl$0_TypeTag true)) (f.20 (store ((as const (Array TypeTag Bool)) \
    false) Box$a1$$Witness$SBox$get$Box$childspec$0_TypeTag true)) (self@7 (MkComposite 0 \
    Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag)) (f.6 (store ((as const (Array \
    TypeTag Bool)) false) $Witness$SBox$get$0_TypeTag true)) (f.22 (store ((as const \
    (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$get$Box$refines$post$0_TypeTag \
    true)))"),
  ("817669",
    "((self@49 (MkComposite 0 Cell_TypeTag)) (self@50 (MkComposite 0 Cell_TypeTag)) (f.31 \
    (store ((as const (Array TypeTag Bool)) false) $Witness$Box$m$0_TypeTag true)) \
    ($heap@68 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) (f.38 (store (store ((as const (Array TypeTag Bool)) \
    false) Box$a1$$Witness$Box$m$0_TypeTag true) SBox$a1$$Witness$Box$m$0_TypeTag true)) \
    (f.35 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$Box$m$impl$0_TypeTag true)) (f.30 (store ((as const (Array TypeTag \
    Bool)) false) $Witness$SBox$m$impl$0_TypeTag true)) (c@47 (MkComposite 0 \
    Cell_TypeTag)) (self@48 (MkComposite 0 Cell_TypeTag)) (f.49 (let ((_let_1 (store ((as \
    const (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$m$impl$0_TypeTag true))) (let \
    ((_let_2 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$Box$m$0_TypeTag true))) (let ((_let_3 (store ((as const (Array \
    TypeTag Bool)) false) Box$a1$$Witness$SBox$m$0_TypeTag true))) (let ((_let_4 (store \
    ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag true))) (let ((_let_5 (store ((as \
    const (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$m$Box$childspec$0_TypeTag \
    true))) (let ((_let_6 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$int_TypeTag true))) (store (store (store (store (store (store (store (store \
    (store (store (store (store (store (store (store (store (store (store (store ((as \
    const (Array TypeTag (Array TypeTag Bool))) (store ((as const (Array TypeTag Bool)) \
    false) $Witness$Box$m$0_TypeTag true)) Cell_TypeTag (store ((as const (Array TypeTag \
    Bool)) false) Cell_TypeTag true)) Box$a1$int_TypeTag _let_6) SBox$a1$int_TypeTag \
    (store _let_6 SBox$a1$int_TypeTag true)) \
    Box$a1$$Witness$SBox$m$Box$childspec$0_TypeTag _let_5) \
    SBox$a1$$Witness$SBox$m$Box$childspec$0_TypeTag (store _let_5 \
    SBox$a1$$Witness$SBox$m$Box$childspec$0_TypeTag true)) \
    Box$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag _let_4) \
    SBox$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag (store _let_4 \
    SBox$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag true)) \
    Box$a1$$Witness$SBox$m$0_TypeTag _let_3) SBox$a1$$Witness$SBox$m$0_TypeTag (store \
    _let_3 SBox$a1$$Witness$SBox$m$0_TypeTag true)) Box$a1$$Witness$Box$m$0_TypeTag \
    _let_2) SBox$a1$$Witness$Box$m$0_TypeTag (store _let_2 \
    SBox$a1$$Witness$Box$m$0_TypeTag true)) Box$a1$$Witness$SBox$m$impl$0_TypeTag _let_1) \
    SBox$a1$$Witness$SBox$m$impl$0_TypeTag (store _let_1 \
    SBox$a1$$Witness$SBox$m$impl$0_TypeTag true)) Box$a1$$Witness$Box$m$impl$0_TypeTag \
    (store ((as const (Array TypeTag Bool)) false) Box$a1$$Witness$Box$m$impl$0_TypeTag \
    true)) $Witness$SBox$m$Box$childspec$0_TypeTag (store ((as const (Array TypeTag \
    Bool)) false) $Witness$SBox$m$Box$childspec$0_TypeTag true)) \
    $Witness$SBox$m$Box$refines$post$0_TypeTag (store ((as const (Array TypeTag Bool)) \
    false) $Witness$SBox$m$Box$refines$post$0_TypeTag true)) $Witness$SBox$m$0_TypeTag \
    (store ((as const (Array TypeTag Bool)) false) $Witness$SBox$m$0_TypeTag true)) \
    $Witness$SBox$m$impl$0_TypeTag (store ((as const (Array TypeTag Bool)) false) \
    $Witness$SBox$m$impl$0_TypeTag true)) $Witness$Box$m$impl$0_TypeTag (store ((as const \
    (Array TypeTag Bool)) false) $Witness$Box$m$impl$0_TypeTag true))))))))) (c@48 \
    (MkComposite 0 Cell_TypeTag)) (c@45 (MkComposite 0 Cell_TypeTag)) ($heap@66 (MkHeap \
    ((as const (Array Composite (Array Field $Box))) ((as const (Array Field $Box)) \
    (BoxInt 0))) 0)) (f.41 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$m$0_TypeTag true)) (f.46 (store (store ((as const (Array TypeTag \
    Bool)) false) Box$a1$int_TypeTag true) SBox$a1$int_TypeTag true)) (c@49 (MkComposite \
    0 Cell_TypeTag)) (self@51 (MkComposite 0 Cell_TypeTag)) (f.39 (store ((as const \
    (Array TypeTag Bool)) false) Box$a1$$Witness$Box$m$0_TypeTag true)) (f.37 (store ((as \
    const (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$m$impl$0_TypeTag true)) \
    ($heap@59 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) ($heap@58 (MkHeap ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (self@47 (MkComposite 0 \
    Cell_TypeTag)) (c@46 (MkComposite 0 Cell_TypeTag)) (self@45 (MkComposite 0 \
    Cell_TypeTag)) (f.45 (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$m$Box$childspec$0_TypeTag true)) (f.36 (store (store ((as const \
    (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$m$impl$0_TypeTag true) \
    SBox$a1$$Witness$SBox$m$impl$0_TypeTag true)) (f.48 (store ((as const (Array TypeTag \
    Bool)) false) Cell_TypeTag true)) (c@50 (MkComposite 0 Cell_TypeTag)) (f.47 (store \
    ((as const (Array TypeTag Bool)) false) Box$a1$int_TypeTag true)) (f.32 (store ((as \
    const (Array TypeTag Bool)) false) $Witness$SBox$m$0_TypeTag true)) (f.40 (store \
    (store ((as const (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$m$0_TypeTag true) \
    SBox$a1$$Witness$SBox$m$0_TypeTag true)) ($heap@63 (MkHeap ((as const (Array \
    Composite (Array Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) \
    ($heap@61 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) ($heap@54 (MkHeap ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) ($heap@51 (MkHeap \
    (store ((as const (Array Composite (Array Field $Box))) ((as const (Array Field \
    $Box)) (BoxInt 0))) (MkComposite 0 Cell_TypeTag) ((as const (Array Field $Box)) \
    (BoxInt 2))) 0)) (f.44 (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$m$Box$childspec$0_TypeTag true) \
    SBox$a1$$Witness$SBox$m$Box$childspec$0_TypeTag true)) (f.33 (store ((as const (Array \
    TypeTag Bool)) false) $Witness$SBox$m$Box$refines$post$0_TypeTag true)) (c@44 \
    (MkComposite (- 1) Cell_TypeTag)) (c@51 (MkComposite 0 Cell_TypeTag)) (f.34 (store \
    ((as const (Array TypeTag Bool)) false) $Witness$SBox$m$Box$childspec$0_TypeTag \
    true)) ($heap@53 (MkHeap (store (store ((as const (Array Composite (Array Field \
    $Box))) (store ((as const (Array Field $Box)) (BoxInt 0)) Cell.v (BoxInt 1))) \
    (MkComposite 0 Cell_TypeTag) (store ((as const (Array Field $Box)) (BoxInt (- 2))) \
    Cell.v (BoxInt 1))) (MkComposite (- 1) Cell_TypeTag) ((as const (Array Field $Box)) \
    (BoxInt (- 1)))) 0)) (f.42 (store (store ((as const (Array TypeTag Bool)) false) \
    Box$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag true) \
    SBox$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag true)) (f.43 (store ((as const \
    (Array TypeTag Bool)) false) Box$a1$$Witness$SBox$m$Box$refines$post$0_TypeTag true)) \
    ($heap@56 (MkHeap ((as const (Array Composite (Array Field $Box))) ((as const (Array \
    Field $Box)) (BoxInt 0))) 0)) ($heap@65 (MkHeap ((as const (Array Composite (Array \
    Field $Box))) ((as const (Array Field $Box)) (BoxInt 0))) 0)) (self@46 (MkComposite 0 \
    Cell_TypeTag)) (self@44 (MkComposite (- 1) Cell_TypeTag)) (f.29 (store ((as const \
    (Array TypeTag Bool)) false) $Witness$Box$m$impl$0_TypeTag true)))")]

/--
info: 610870: kept 12 of 12 (before: 0)
481474: kept 2 of 2 (before: 0)
369786: kept 11 of 11 (before: 0)
374814: kept 11 of 11 (before: 0)
217029: kept 13 of 13 (before: 0)
834557: kept 10 of 10 (before: 0)
334253: kept 11 of 11 (before: 0)
862724: kept 10 of 10 (before: 0)
549406: kept 8 of 8 (before: 0)
332749: kept 2 of 2 (before: 0)
263064: kept 16 of 16 (before: 0)
651595: kept 22 of 22 (before: 0)
817669: kept 48 of 48 (before: 0)
-/
#guard_msgs in
#eval show IO Unit from do
  for (label, resp) in lostAnswers do
    kept label resp

end ModelCoverageCR1Test

end
