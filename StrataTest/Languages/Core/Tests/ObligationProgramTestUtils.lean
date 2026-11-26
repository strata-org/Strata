/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.Passive.CoreWPSSA
import Strata.Languages.Core.Factory
import Strata.Languages.Core
import Plausible

/-! # Test helpers for the phases on obligation programs

Expression and statement builders over integer variables, the output of the WP and SSA phases on
a statement list (`obligations`), random statement lists for Plausible (`RProg`), and the SMT
queries `--vcgen wp` writes for a program (`wpQueries`), shared by the tests of guard forwarding,
of the inlining of single-use definitions and of guard propagation. -/

namespace ObligationProgramTestUtils

open Core Lambda Imperative Imperative.WP Core.WP

def id' (name : String) : CoreIdent := ⟨name, ()⟩
def int (n : Int) : Expression.Expr := .intConst Core.valueLoc n
def md : MetaData Expression := #[]
def iv (n : String) : Expression.Expr := .fvar Core.valueLoc (id' n) (some .int)
def gt (a b : Expression.Expr) : Expression.Expr := .app Core.valueLoc (.app Core.valueLoc intGtOp a) b
def add (a b : Expression.Expr) : Expression.Expr := .app Core.valueLoc (.app Core.valueLoc intAddOp a) b
/-- `init x : int := e`. -/
def initInt (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] .int) (.det e) md))
def assert' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assert l e md))
def ndIte (t e : Statements) : Statement := .ite .nondet t e md
def set' (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.set (id' x) (.det e) md))
def ite' (c : Expression.Expr) (t e : Statements) : Statement := .ite (.det c) t e md
def block' (l : String) (ss : Statements) : Statement := .block l ss md
def exit' (l : String) : Statement := .exit l md
def ci (i : Nat) : Expression.Expr := .eq Core.valueLoc (iv "c") (int i)

/-- The lines `ls` joined by newlines. -/
def lines (ls : List String) : String := "\n".intercalate ls

/-- A procedure `P` with integer parameters `params` and body `ss`. -/
def proc (params : List String) (ss : Statements) : Procedure := {
    header := { name := id' "P", typeArgs := [],
                inputs := params.map (fun x => (id' x, (.int : LMonoTy))), outputs := [] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured ss false }

/-- The output of the WP and SSA phases on `ss`, the empty list on error. -/
def obligations (params : List String) (ss : Statements) : Statements :=
  match (do
      let w ← wpEntry (P := Expression) (IdSet.ofList []) (proc params ss).paramTys ss
      let (_, so) ← ssaLoopFree Lambda.Factory.default (IdSet.ofList []) (proc params ss) w.lay
      pure so.out : Except String Statements) with
  | .ok o => o
  | .error _ => []

/-! ## Random statement lists -/

/-- An expression of a random statement list: an integer variable `x(i % 3)`, a literal, a sum,
    a conditional, `c == n`, a comparison, or an equality of two variables. -/
inductive RExp where
  | v (i : Nat) | k (n : Nat) | add (a b : RExp) | ite (c a b : RExp) | eqc (n : Nat)
  | gt (a b : RExp) | eqv (i j : Nat)
  deriving Repr

/-- A statement of a random statement list; `exitIf` exits the innermost block, if any. -/
inductive RStmt where
  | set (x : Nat) (e : RExp) | ite (c : RExp) (t f : List RStmt) | nd (t f : List RStmt)
  | blk (b : List RStmt) | exitIf (c : RExp) | assert (c : RExp) | assume (c : RExp)
  deriving Repr

/-- A random statement list. -/
structure RProg where
  body : List RStmt
  deriving Repr

/-- The variable `x(i % 3)`. -/
def rv (i : Nat) : String := s!"x{i % 3}"

/-- The Core expression of `e`. -/
def RExp.toE : RExp → Expression.Expr
  | .v i => iv (rv i) | .k n => int n | .add a b => .app Core.valueLoc (.app Core.valueLoc intAddOp a.toE) b.toE
  | .ite c a b => .ite Core.valueLoc c.toE a.toE b.toE | .eqc n => ci n
  | .gt a b => .app Core.valueLoc (.app Core.valueLoc intGtOp a.toE) b.toE
  | .eqv i j => .eq Core.valueLoc (iv (rv i)) (iv (rv j))

mutual
/-- The Core statements of `s`, in the innermost block `l`, with label prefix `p`. -/
def RStmt.toS (l : Option String) (p : String) : RStmt → Statements
  | .set x e => [set' (rv x) e.toE]
  | .ite c t f => [ite' c.toE (rToS l (p ++ "t") t) (rToS l (p ++ "f") f)]
  | .nd t f => [ndIte (rToS l (p ++ "t") t) (rToS l (p ++ "f") f)]
  | .blk b => [block' ("L" ++ p) (rToS (some ("L" ++ p)) (p ++ "b") b)]
  | .exitIf c => l.toList.map fun l => ite' c.toE [exit' l] []
  | .assert c => [assert' ("a" ++ p) c.toE]
  | .assume c => [.cmd (.cmd (.assume ("u" ++ p) c.toE md))]
/-- The Core statements of `ss`, in the innermost block `l`, with label prefix `p`. -/
def rToS (l : Option String) (p : String) : List RStmt → Statements
  | [] => []
  | s :: r => s.toS l (p ++ "0") ++ rToS l (p ++ "1") r
end

/-- The statement list of `r`: `x0`, `x1`, `x2` defined from `c`, `0` and `1`, the body, and
    an assertion over the three. -/
def RProg.stmts (r : RProg) : Statements :=
  [initInt "x0" (iv "c"), initInt "x1" (int 0), initInt "x2" (int 1)] ++ rToS none "p" r.body ++
    [assert' "end" (gt (add (iv "x0") (add (iv "x1") (iv "x2"))) (int 0))]

open Plausible

/-- A random condition over the random expressions `g`. -/
def genC (g : Gen RExp) : Gen RExp := Gen.oneOfWithDefault (pure (.eqc 0))
  [(.eqc ·) <$> Gen.chooseNat, (.gt · ·) <$> g <*> g,
    (.eqv · ·) <$> Gen.chooseNat <*> Gen.chooseNat]

/-- A random expression of depth at most `n + 1`. -/
def genE : Nat → Gen RExp
  | 0 => Gen.oneOfWithDefault (pure (.k 0)) [(.v ·) <$> Gen.chooseNat, (.k ·) <$> Gen.chooseNat]
  | n + 1 => Gen.frequency (genE 0) [(3, genE 0), (2, (.add · ·) <$> genE n <*> genE n),
      (1, (.ite · · ·) <$> genC (genE n) <*> genE n <*> genE n)]

/-- A random condition of depth at most 3. -/
def genC1 : Gen RExp := genC (genE 1)

mutual
/-- A random statement of nesting depth at most `n`. -/
def genS : Nat → Gen RStmt
  | 0 => (.set · ·) <$> Gen.chooseNat <*> genE 1
  | n + 1 => Gen.frequency (genS 0) [(4, (.set · ·) <$> Gen.chooseNat <*> genE 2),
      (2, (.ite · · ·) <$> genC1 <*> genL n <*> genL n), (1, (.nd · ·) <$> genL n <*> genL n),
      (1, (.blk ·) <$> genL n), (2, (.exitIf ·) <$> genC1), (2, (.assert ·) <$> genC1),
      (1, (.assume ·) <$> genC1)]
/-- A random list of at most four statements of nesting depth less than `n`. -/
def genL : Nat → Gen (List RStmt)
  | 0 => pure []
  | n + 1 => do (List.range (← Gen.choose Nat 0 4 (by omega)).1).mapM fun _ => genS n
end

instance : Arbitrary RProg := ⟨RProg.mk <$> genL 4⟩
instance : Shrinkable RProg :=
  ⟨fun r => (List.range r.body.length).map fun i => ⟨r.body.eraseIdx i⟩⟩

/-- The SMT queries `--vcgen wp` writes for `pgm`, concatenated: `pgm` is verified without a
    solver (`skipSolver`) into the fresh directory `vcDir`, through `pipeline` when one is given
    and in the default order of `--vcgen wp` otherwise; the `.smt2` files are read back and
    `vcDir` is removed. -/
def wpQueries (pgm : StrataDDM.Program) (vcDir : System.FilePath)
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none) :
    IO String := do
  if ← vcDir.pathExists then
    IO.FS.removeDirAll vcDir
  IO.FS.createDirAll vcDir
  let opts : Core.VerifyOptions := { Core.VerifyOptions.quiet with
    vcgen := .wp
    skipSolver := true
    vcDirectory := some vcDir }
  let _ ← Strata.Core.verify pgm (options := opts) (pipeline := pipeline)
  let mut out := ""
  for e in ← vcDir.readDir do
    if e.fileName.endsWith ".smt2" then
      out := out ++ (← IO.FS.readFile e.path)
  IO.FS.removeDirAll vcDir
  return out

end ObligationProgramTestUtils
