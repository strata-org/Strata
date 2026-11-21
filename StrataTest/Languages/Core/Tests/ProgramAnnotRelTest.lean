/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.Verifier

/-! # Test for the annotations `Core.typeCheck` changes

A program built as an AST: a type synonym, a function whose signature uses it, and a procedure
declaring a variable at a written type variable. The checker resolves the synonym in the
signature and instantiates the type variable, and the checked program erases to the same program
as the written one (`Core.typeCheck_eraseAnnots`).
-/

namespace Core.ProgramAnnotRelTest
open Lambda

private def x : CoreIdent := ⟨"x", ()⟩

/-- Prints the checked form of `prog` and whether it erases like `prog`. -/
private def report (prog : Program) : IO Unit :=
  match Core.typeCheck .quiet prog with
  | .ok checked => do
    IO.println (Std.format checked)
    IO.println s!"erasures agree: {checked.eraseAnnots == prog.eraseAnnots}"
  | .error e => IO.println s!"error: {e.message}"

/-- `function f (x : T) : T { x }`, with `T := int`. -/
private def program : Program :=
  { decls :=
    [ .type (.syn { name := "T", typeArgs := [], type := .int }) #[],
      .func { name := ⟨"f", ()⟩, inputs := [(x, .tcons "T" [])], output := .tcons "T" [],
              body := some (.fvar coreLoc x none) } #[],
      .proc { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured
                [Statement.init x (.forAll [] (.ftvar "a")) (.det (.const coreLoc (.intConst 1)))
                  #[]] false } #[] ] }

/--
info: program Core;

type T := int;
function f (x : int) : int {
  x
}
procedure p ()
{
  var x : int := 1;
};

erasures agree: true
-/
#guard_msgs in
#eval report program

private def tt : Expression.Expr := .const coreLoc (.boolConst true)
private def one : Expression.Expr := .const coreLoc (.intConst 1)
private def y : CoreIdent := ⟨"y", ()⟩

private def emptySpec : Procedure.Spec := { preconditions := [], postconditions := [] }

/-! ## A function whose type parameter has a reserved name is renamed -/

private def reservedFunc : Program :=
  { decls :=
    [ .func { name := ⟨"f", ()⟩, typeArgs := ["$__ty0"], inputs := [(x, .ftvar "$__ty0")],
              output := .ftvar "$__ty0", body := some (.fvar coreLoc x none) } #[] ] }

/--
info: program Core;

function f<a> (x : a) : a {
  x
}

erasures agree: true
-/
#guard_msgs in
#eval report reservedFunc

/-! ## A procedure with a type parameter, a local of that type and a nested `init` -/

private def typeParamProc : Program :=
  { decls :=
    [ .proc { header := { name := ⟨"p", ()⟩, typeArgs := ["a"], inputs := [], outputs := [] },
              spec := emptySpec,
              body := .structured
                [Statement.init y (.forAll [] (.ftvar "a")) .nondet #[],
                 Imperative.Stmt.ite (.det tt)
                   [Statement.init ⟨"z", ()⟩ (.forAll [] .int) (.det one) #[]] [] #[]] false }
            #[] ] }

/--
info: program Core;

procedure p<a> ()
{
  var y : a;
  if (true) {
    var z : int := 1;
  }
};

erasures agree: true
-/
#guard_msgs in
#eval report typeParamProc

/-! ## A datatype constructor field written with a synonym is resolved -/

private def synonymField : Program :=
  { decls :=
    [ .type (.syn { name := "T", typeArgs := [], type := .int }) #[],
      .type (.data
        [{ name := "Box", typeArgs := [],
           constrs := [{ name := ⟨"Mk", ()⟩, args := [(⟨"v", ()⟩, .tcons "T" [])] }],
           constrs_ne := rfl }]) #[] ] }

/--
info: program Core;

type T := int;
datatype Box {
  Mk(v : int)
};

erasures agree: true
-/
#guard_msgs in
#eval report synonymField

/-! ## A procedure with a control flow graph body -/

private def cfgProc : Program :=
  { decls :=
    [ .proc { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
              spec := emptySpec,
              body := .cfg
                { entry := "l0",
                  blocks :=
                    [("l0", ⟨[.cmd (.init y (.forAll [] (.ftvar "a")) (.det one) #[])],
                        .condGoto tt "l1" "l2" #[], #[]⟩),
                     ("l1", ⟨[], .finish #[], #[]⟩), ("l2", ⟨[], .finish #[], #[]⟩)] } false }
            #[] ] }

/--
info: program Core;

procedure p ()
cfg l0 {
  l0: {
    var y : int := 1;
    branch (true) goto l1 else goto l2;
  }
  l1: {
    return;
  }
  l2: {
    return;
  }
};

erasures agree: true
-/
#guard_msgs in
#eval report cfgProc

/-! ## A lemma with a type parameter -/

private def typeParamLemma : Program :=
  { decls :=
    [ .lemma { name := "l", typeArgs := ["$__ty0"], e := .eq coreLoc one one } #[] ] }

/--
info: program Core;

lemma [l] <a>: 1 == 1;

erasures agree: true
-/
#guard_msgs in
#eval report typeParamLemma

/-! ## A recursive function block -/

private def recBlock : Program :=
  { decls :=
    [ .recFuncBlock
      [{ name := ⟨"f", ()⟩, isRecursive := true, inputs := [(x, .int)], output := .int,
         body := some (.app coreLoc (.op coreLoc ⟨"f", ()⟩ none) (.fvar coreLoc x none)) }]
      #[] ] }

/--
info: program Core;

rec function f (x : int) : int
{
  f(x)
};

erasures agree: true
-/
#guard_msgs in
#eval report recBlock

/-! ## A call of a polymorphic procedure -/

/-- A polymorphic procedure `id<a>` and a procedure that calls it with written type arguments
`none`, on an integer argument. -/
private def callPoly : Program :=
  { decls :=
    [ .proc { header := { name := ⟨"id", ()⟩, typeArgs := ["a"], inputs := [(x, .ftvar "a")],
                          outputs := [(y, .ftvar "a")] },
              spec := emptySpec,
              body := .structured [] false } #[],
      .proc { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
              spec := emptySpec,
              body := .structured
                [Statement.init y (.forAll [] .int) .nondet #[],
                 .cmd (.call "id" none [.inArg one, .outArg y] #[])] false } #[] ] }

/--
info: program Core;

procedure id<a> (x : a, out y : a)
{
  
};
procedure p ()
{
  var y : int;
  call id(1, out y);
};

erasures agree: true
-/
#guard_msgs in
#eval report callPoly

/-- The type arguments the checked call of `callPoly` stores, as strings. -/
private def callPolyTyArgs : IO Unit :=
  match Core.typeCheck .quiet callPoly with
  | .ok checked =>
    match checked.decls with
    | [_, .proc q _] =>
      match q.body with
      | .structured [_, .cmd (.call _ tyArgs _ _)] _ =>
        IO.println s!"{tyArgs.map (·.map toString)}"
      | _ => IO.println "unexpected body"
    | _ => IO.println "unexpected declarations"
  | .error e => IO.println s!"error: {e.message}"

/-- info: (some [Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "int" [])]) -/
#guard_msgs in
#eval callPolyTyArgs

/-! ## A change to a constant is not an annotation change -/

/-- The program `typeParamProc` with the constant `1` written as `2`. -/
private def changedConst : Program :=
  { decls :=
    [ .proc { header := { name := ⟨"p", ()⟩, typeArgs := ["a"], inputs := [], outputs := [] },
              spec := emptySpec,
              body := .structured
                [Statement.init y (.forAll [] (.ftvar "a")) .nondet #[],
                 Imperative.Stmt.ite (.det tt)
                   [Statement.init ⟨"z", ()⟩ (.forAll [] .int)
                     (.det (.const coreLoc (.intConst 2))) #[]] [] #[]] false } #[] ] }

/-- info: erasures agree: false -/
#guard_msgs in
#eval match Core.typeCheck .quiet typeParamProc with
  | .ok checked => IO.println s!"erasures agree: {checked.eraseAnnots == changedConst.eraseAnnots}"
  | .error e => IO.println s!"error: {e.message}"

end Core.ProgramAnnotRelTest
