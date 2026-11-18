/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.DDMTransform.Translate

/-! # Helpers shared by the Core type-checking tests -/

public section

namespace Core.TestUtil

open Lambda

/-- A nullary type constant named with the rigid prefix (`$__rigid_a`). -/
def rigidA : LMonoTy := .tcons (Core.skolemName "a") []

/-- The type variable `a`. -/
def tv (a : String) : LMonoTy := .ftvar a

/-- The identifier `x`. -/
def xId : CoreIdent := ⟨"x", ()⟩

/-- The identifier `y`. -/
def yId : CoreIdent := ⟨"y", ()⟩

/-- The text of `s` before its first line break. -/
def firstLine (s : String) : String := (s.splitOn "\n").headD s

/-- The first line of a rendered message, dropping the listing of registered types that follows
    some type errors: the listing follows hash-map order. -/
def firstLineOf (f : Std.Format) : Std.Format := firstLine (toString f)

/-- The Core program a `#strata` program translates to, keeping its metadata. -/
def translateWithMetaData (p : StrataDDM.Program) : Core.Program :=
  (Strata.TransM.run Inhabited.default (Strata.translateProgram p)).fst

/-- The Core program a `#strata` program translates to, without metadata. -/
def translate (p : StrataDDM.Program) : Core.Program :=
  (translateWithMetaData p).stripMetaData

/-- The type environment `Core.typeCheck` starts from. -/
def Env0 : Expression.TyEnv := Lambda.TEnv.default

/-- The default type environment with one empty scope pushed, as for checking statements. -/
def stmtEnv : Expression.TyEnv := (Lambda.TEnv.default (IDMeta := Unit)).pushEmptyContext

/-- The default type environment with exactly the given type aliases. -/
def aliasEnv (aliases : List TypeAlias) : Expression.TyEnv :=
  TEnv.default.updateContext { TEnv.default.context with aliases }

/-- `ACCEPTED` when a check succeeds, or `REJECTED:` followed by the error it reports. -/
def verdictOf {ε α : Type} [ToString ε] (result : Except ε α) : Std.Format :=
  match result with
  | .ok _ => "ACCEPTED"
  | .error e => s!"REJECTED: {e}"

/-- `ACCEPTED:` followed by `shown` applied to the result when a check succeeds,
    or `REJECTED:` followed by the error it reports. -/
def verdictWith {ε α : Type} [ToString ε] (shown : α → Std.Format)
    (result : Except ε α) : Std.Format :=
  match result with
  | .ok a => f!"ACCEPTED: {shown a}"
  | .error e => s!"REJECTED: {e}"

/-- `ACCEPTED` when a check succeeds, or `REJECTED:` followed by the first
    line of the error it reports. -/
def firstLineVerdict {ε α : Type} [ToString ε] (result : Except ε α) : Std.Format :=
  firstLineOf (verdictOf result)

/-- The program checker's verdict, with the message of any rejection. -/
def programVerdict (program : Program) (C : Expression.TyContext := initTyContext)
    (Env : Expression.TyEnv := Lambda.TEnv.default) : Std.Format :=
  verdictOf (Core.Program.typeCheck C Env program)

/-- The function checker's verdict, with the message of any rejection. -/
def functionVerdict (func : Function) (C : Expression.TyContext := initTyContext)
    (Env : Expression.TyEnv := Lambda.TEnv.default) : Std.Format :=
  verdictOf (Core.Function.typeCheck C Env func)

/-- The procedure checker's verdict on `proc` alone, with the message of any
    rejection. -/
def procedureVerdict (proc : Procedure) (C : Expression.TyContext := initTyContext)
    (Env : Expression.TyEnv := Lambda.TEnv.default) : Std.Format :=
  verdictOf (Core.Procedure.typeCheck C Env Program.init proc .empty)

/-- The verdict of `Core.typeCheck` on `program` with the builtin functions
    or `factory`, plus the extra functions `moreFns`. A rejection shows its
    message but not its range. -/
def coreVerdict (program : Program) (factory : Option (Lambda.Factory CoreLParams) := none)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) : Std.Format :=
  verdictOf ((Core.typeCheck .quiet program factory moreFns).mapError (·.message))

/-- Prints each verdict on its own line. -/
def printEach (verdicts : List Std.Format) : IO Unit :=
  for v in verdicts do IO.println v

/-- `var x : ty := *`. -/
def declNondet (x : String) (ty : LMonoTy) : Statement :=
  Statement.init x (.forAll [] ty) .nondet .empty

/-- The procedure `name<typeArgs>(inputs, out outputs)` with body `body`,
    preconditions `pre` and postconditions `post`. Its `n`-th conditions are
    labeled `<name>_requires_<n>` and `<name>_ensures_<n>`, as in concrete
    syntax. -/
def mkProc (name : String) (typeArgs : List TyIdentifier)
    (inputs outputs : @LMonoTySignature Unit) (body : List Statement := [])
    (pre post : List Expression.Expr := []) : Decl :=
  let conds (kind : String) (es : List Expression.Expr) :=
    es.zipIdx.map fun (e, n) => (s!"{name}_{kind}_{n}", ⟨e, .Default, #[]⟩)
  .proc { header := { name := ⟨name, ()⟩, typeArgs, inputs, outputs },
          spec := { preconditions := conds "requires" pre,
                    postconditions := conds "ensures" post },
          body := .structured body } .empty

/-- `datatype List (a : Type) { Nil(), Cons(hd : a, tl : List a) }`. -/
def listDecl : Decl :=
  .type (.data [{
    name := "List", typeArgs := ["a"],
    constrs := [
      { name := ⟨"Nil", ()⟩, args := [], testerName := "List..isNil" },
      { name := ⟨"Cons", ()⟩,
        args := [(⟨"hd", ()⟩, .ftvar "a"),
                 (⟨"tl", ()⟩, .tcons "List" [.ftvar "a"])],
        testerName := "List..isCons" }],
    constrs_ne := rfl }]) .empty

/-- `x := e`. -/
def setS (x : String) (e : Expression.Expr) : Statement := Statement.set x e .empty

/-- `call p(args)`. -/
def callS (p : String) (args : List (Imperative.CallArg Expression)) : Statement :=
  Statement.call p args .empty

/-- An unannotated occurrence of the variable `x`. -/
def var (x : String) : Expression.Expr := LExpr.fvar Core.coreLoc x none

/-- A universal quantifier whose body may refer to its binder at de Bruijn index zero. -/
def allOf (ty : Option LMonoTy) (body : Expression.Expr) : Expression.Expr :=
  LExpr.all Core.coreLoc "x" ty body

/-- An occurrence named like the resolver's first generated expression binder. -/
def generatedBinderOccurrence : Expression.Expr :=
  .fvar Core.coreLoc ⟨"$__var0", ()⟩ none

/-- A polymorphic nullary function whose result type each use must determine. -/
def anyFunction : Function :=
  { name := ⟨"any", ()⟩, typeArgs := ["a"], inputs := [], output := .ftvar "a" }

/-- The identity function `idf : ∀x. x → x`. -/
def idfDecl : Decl :=
  .func { name := "idf", typeArgs := ["x"], inputs := [("y", .ftvar "x")],
          output := .ftvar "x" } .empty

/-- `idf true == true`, with `ann` annotating `idf`. -/
def idfTrueEq (ann : Option LMonoTy) : Expression.Expr :=
  .eq Core.coreLoc (.app Core.coreLoc (.op Core.coreLoc ⟨"idf", ()⟩ ann)
                    (.boolConst Core.coreLoc true)) (.boolConst Core.coreLoc true)

/-- The `idf` annotations `a → a`, `c → c` and none. -/
def idfAnnots : List (Option LMonoTy) :=
  [some (.arrow (.ftvar "a") (.ftvar "a")), some (.arrow (.ftvar "c") (.ftvar "c")), none]

/-- Prints the verdict on `build ann` in context `C` for each `idf` annotation `ann`. -/
def printIdfVerdicts (build : Option LMonoTy → Program)
    (C : Expression.TyContext := initTyContext) : IO Unit :=
  printEach (idfAnnots.map fun ann => programVerdict (build ann) C)

end Core.TestUtil

end
