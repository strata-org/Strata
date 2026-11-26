/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import Strata.Languages.Core.DDMTransform.Translate
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataTest.Languages.Core.Tests.RandomPrograms

/-! # The random programs are well-formed, and survive printing and parsing

Every program of `generate` is well-typed by construction, so each must type-check; and
it is built as the DDM translation builds programs, so printing it with
`Core.formatProgram` and parsing the text must give the same program back, up to metadata
and expression locations. A program that fails either is a bug in the generator, or in
Core's type checker, printer, parser or translation. The tests check both on seeds 0 to 199,
show the program of one seed, check that programs of one, two and three procedures are
about equally common, and check that every kind of statement, guard and operator the
generator documents occurs, and that no program repeats an assertion label. -/

meta section

namespace Core.RandomProgramsTest

open Core.RandomPrograms

/-- `text`, as `Core.formatProgram` prints a program, parsed and translated. -/
def parse (text : String) : IO (Except String Program) := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Strata.Core]
  let body := if text.startsWith "program Core;" then text.drop 13 else text
  try
    let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core"
      (StrataDDM.Parser.stringInputContext ⟨"randomProgram"⟩ body.toString)
    let (program, errors) := Strata.TransM.run Inhabited.default (Strata.translateProgram sp)
    if errors.isEmpty then return .ok program
    return .error s!"translation errors: {repr errors}"
  catch e => return .error s!"{e}"

mutual
/-- `s` with empty metadata, its commands' included. -/
def stmtNoMd : Statement → Statement
  | .cmd (.cmd c) => .cmd (.cmd (match c with
    | .init x ty e _ => .init x ty e #[]
    | .set x e _ => .set x e #[]
    | .assert l e _ => .assert l e #[]
    | .assume l e _ => .assume l e #[]
    | .cover l e _ => .cover l e #[]))
  | .block l b _ => .block l (stmtsNoMd b) #[]
  | .ite c t f _ => .ite c (stmtsNoMd t) (stmtsNoMd f) #[]
  | .exit l _ => .exit l #[]
  | s => s

/-- `ss` with empty metadata. -/
def stmtsNoMd : List Statement → List Statement
  | [] => []
  | s :: ss => stmtNoMd s :: stmtsNoMd ss
end

/-- `p` with empty metadata and every expression's location erased (`Core.eraseLocs`): the
    translation fills both with source positions, and the generator with placeholders. -/
def noMd (p : Program) : Program :=
  { decls := p.decls.map fun
      | .proc q _ =>
        let q := Procedure.mapExprs eraseLocs q
        .proc { q with body := match q.body with
          | .structured ss o => .structured (stmtsNoMd ss) o
          | b => b } #[]
      | d => d }

/-- The seeds `first`, …, `first + count - 1` whose program does not type-check, or does
    not come back the same from printing and parsing, each with what went wrong. -/
def illFormed (first count : Nat) : IO (List (Nat × String)) := do
  let mut bad := []
  for seed in [first:first + count] do
    let p := generate seed
    if let .error e := Core.typeCheck .quiet p then
      bad := bad ++ [(seed, e.message)]
    else match ← parse (toString (Strata.Core.formatProgram p)) with
      | .error e => bad := bad ++ [(seed, e)]
      | .ok q => unless noMd q == noMd p do bad := bad ++ [(seed, "printed and parsed, it differs")]
  return bad

/-- info: [] -/
#guard_msgs in
#eval illFormed 0 200

/-- info: program Core;

procedure p0 (a : bool)
{
  assert [a0]: a;
};
procedure p1 (a : bool, b : int)
{
  assert [a1]: int.le(b, b);
};
-/
#guard_msgs in
#eval IO.println (Strata.Core.formatProgram (generate 118))

/-- The number of programs of one, two and three procedures among seeds 0 to 299. Each is
    about a hundred; if `GenState.ofSeed` kept the first random number, every program would
    have three procedures. -/
def procedureCounts : List Nat :=
  let lengths := (List.range 300).map fun seed => (generate seed).decls.length
  [1, 2, 3].map lengths.count

#guard procedureCounts.all (· ≥ 80)

/-- The kinds of operator and expression in `e`: each operator's name, `ite` and `==`. -/
partial def exprKinds : Expression.Expr → List String
  | .op _ o _ => [o.name]
  | .app _ f a => exprKinds f ++ exprKinds a
  | .ite _ c t e => "ite" :: (exprKinds c ++ exprKinds t ++ exprKinds e)
  | .eq _ a b => "==" :: (exprKinds a ++ exprKinds b)
  | _ => []

/-- The kinds of statement and guard in `s`, and of expression in them. -/
partial def stmtKinds : Statement → List String
  | .init _ _ (.det e) _ => "init" :: exprKinds e
  | .init _ _ .nondet _ => ["init without a value"]
  | .set _ e _ => "set" :: exprKinds e
  | .havoc _ _ => ["havoc"]
  | .assert _ e _ => "assert" :: exprKinds e
  | .assume _ (.const _ (.boolConst false)) _ => ["assume false"]
  | .assume _ e _ => "assume" :: exprKinds e
  | .ite (.det (.const _ (.boolConst _))) t f _ => "if on a constant" :: (t ++ f).flatMap stmtKinds
  | .ite (.det c) t f _ => "if" :: (exprKinds c ++ (t ++ f).flatMap stmtKinds)
  | .ite .nondet t f _ => "if nondeterministic" :: (t ++ f).flatMap stmtKinds
  | .block _ b _ => "block" :: b.flatMap stmtKinds
  | .exit _ _ => ["exit"]
  | _ => []

/-- The structured bodies of `p`. -/
def bodies (p : Program) : List (List Statement) :=
  p.decls.filterMap fun
    | .proc q _ => match q.body with | .structured ss _ => some ss | _ => none
    | _ => none

/-- The kinds the module documentation promises, missing from every program of seeds 0 to
    199: a weight dropped to zero, or a case lost in a refactoring, shows here. A kind that
    another case also makes shows only when every case making it is lost: a constant guard and
    `assume false` (a literal leaf), `if` and `==` (the guard `v == v`), `Int.Neg` (a negative
    literal), `Bool.Not` (`!=`). -/
def missingKinds : List String :=
  let seen := (List.range 200).flatMap fun seed => (bodies (generate seed)).flatten.flatMap stmtKinds
  let ops := [intAddOp, intSubOp, intMulOp, intNegOp, intDivOp, intModOp, intDivTOp, intModTOp,
    intLtOp, intLeOp, intGtOp, intGeOp, boolNotOp, boolAndOp, boolOrOp, boolImpliesOp,
    boolEquivOp].filterMap fun | .op _ o _ => some o.name | _ => none
  (["init", "init without a value", "set", "havoc", "assert", "assume", "assume false", "if",
    "if on a constant", "if nondeterministic", "block", "exit", "ite", "=="] ++ ops).filter
    (!seen.contains ·)

/-- info: [] -/
#guard_msgs in
#eval missingKinds

/-- The seeds among 0 to 199 whose program repeats an assertion label. -/
def repeatedLabels : List Nat :=
  (List.range 200).filter fun seed =>
    let labels := ((bodies (generate seed)).flatMap Statements.collectAssertIds).map (·.label)
    labels.eraseDups.length != labels.length

#guard repeatedLabels.isEmpty

end Core.RandomProgramsTest

end
