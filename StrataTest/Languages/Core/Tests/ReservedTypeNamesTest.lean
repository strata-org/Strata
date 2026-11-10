/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # Program names with reserved prefixes

Type checking and later passes generate types and type variables whose names
start with a reserved prefix (`Lambda.reservedNamePrefixes`). A program may use
such names too: a pass that generates a type name skips the names the program
declares, and type checking renames a function type parameter with a reserved
prefix before it generates type variables. These tests check that no program
name is taken for a generated one.
-/

meta section
namespace Strata.ReservedTypeNamesTest

def typeCheckMessage (p : Core.Program) : String :=
  match _root_.Core.typeCheck .quiet p with
  | .ok _ => "ok"
  | .error e => e.message

/-! A declared type named like the opaque type that closes a lemma's free type
variable is not taken for it. Here the axiom makes that type a singleton, under
which the lemma would hold; the lemma is false, so it must not verify. -/

def capturedLemmaType :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
function first<a> (xs : MyList a) : a;
function second<a> (xs : MyList a) : a;
type $__free_nil_refl_0;
axiom [single]: forall x : $__free_nil_refl_0, y : $__free_nil_refl_0 :: x == y;
lemma [nil_refl]: first(Nil()) == second(Nil());
#end

/--
info:
Obligation: nil_refl
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify capturedLemmaType (options := .quiet)

/-! The lemma's free type is closed with a type of its own, not the declared
one. -/

/-- info: [MyList, $__free_nil_refl_0, $__free_nil_refl_0_1] -/
#guard_msgs in
#eval match _root_.Core.typeCheck .quiet (Core.getProgram capturedLemmaType).fst with
  | .ok p => IO.println (p.decls.filterMap fun (d : Core.Decl) =>
      d.getTypeDecl?.map fun (td : Core.TypeDecl) => td.name.name)
  | .error e => IO.println e.message

/-! The verdict is the one the same program gets with an unreserved type name:
the solver's counterexample cannot be checked against the quantified axiom, so
the result is unknown rather than a failure, and it is not a proof. -/

def unreservedSingleton :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
function first<a> (xs : MyList a) : a;
function second<a> (xs : MyList a) : a;
type Single;
axiom [single]: forall x : Single, y : Single :: x == y;
lemma [nil_refl]: first(Nil()) == second(Nil());
#end

/--
info:
Obligation: nil_refl
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify unreservedSingleton (options := .quiet)

/-! A declared type named like the opaque type that replaces a procedure's type
parameter is not taken for it either. -/

def declaredOpaqueName :=
#strata
program Core;
type $__opaque_P_a_0;
procedure P<a> (x : a, y : $__opaque_P_a_0) {
  assert [refl]: (x == x);
};
#end

/--
info:
Obligation: refl
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify declaredOpaqueName (options := .quiet)

/-! A declared type synonym named like the rigid type that stands for a lemma's
type parameter during type checking is not taken for it: if it were, `a` would
be `int` and the lemma would be accepted. -/

def declaredRigidName :=
#strata
program Core;
type $__rigid_bad_a := int;
lemma [bad] <a> (x : a): x == 0;
#end

/-- info: "Impossible to unify $__rigid_bad_a_1 with int." -/
#guard_msgs in
#eval typeCheckMessage (Core.getProgram declaredRigidName).fst

/-! A function type parameter with a reserved prefix is renamed, so the
function type checks and keeps its meaning. -/

def reservedTypeParam :=
#strata
program Core;
function id<$__ty0> (x : $__ty0) : $__ty0 { x }
procedure P () {
  assert [id_one]: (id(1) == 1);
};
#end

/--
info:
Obligation: id_one
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify reservedTypeParam (options := .quiet)

/-! The new name of a renamed type parameter avoids the function's other type
variables, including undeclared ones, so an undeclared `a` is still reported.
The parser rejects such a function, so it is built directly, as a front end
would. -/

def renamedAvoidsUndeclared : Core.Decl :=
  .func { name := ⟨"f", ()⟩, typeArgs := ["$__ty0"],
          inputs := [(⟨"x", ()⟩, .ftvar "$__ty0")], output := .ftvar "a" } .empty

/-- info: "Function 'f': type variables [a] appear in the signature but are not declared in typeArgs [a_1]" -/
#guard_msgs in
#eval typeCheckMessage { decls := [renamedAvoidsUndeclared] }

/-! The generated types do not stop a program from type checking again. Here
the opaque-type pass, type checking (which closes the lemma's free element type
of `Nil()` with a generated type), monomorphization and simplification run first,
then type checking again. -/

def polyProgram :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
lemma [nil_refl]: Nil() == Nil();
procedure P<a> (x : a) {
  assert [refl]: (x == x);
};
#end

def typeCheckAfterPipeline (p : Core.Program) : IO String := do
  let phases := Core.preSymbolicEvalPipelinePhases .quiet ++ [Core.typeCheckPipelinePhase .quiet]
  match ← (Core.runTransforms p phases).toBaseIO with
  | .ok (p, _) =>
    return toString (p.decls.filterMap fun (d : Core.Decl) =>
      d.getTypeDecl?.map fun (td : Core.TypeDecl) => td.name.name)
  | .error e => return e.message

/-- info: "[MyList, $__free_nil_refl_0, $__opaque_P_a_0]" -/
#guard_msgs in
#eval typeCheckAfterPipeline (Core.getProgram polyProgram).fst

/-! A type declared twice is rejected, whatever kinds the two declarations
have. The parser already rejects a source program that does this, so these
programs are built directly, as a front end or a pass would. -/

def fooCon : Core.Decl := .type (.con { name := "Foo", params := [] }) .empty
def fooSyn : Core.Decl := .type (.syn { name := "Foo", typeArgs := [], type := .int }) .empty

/-- info: "Error in type Foo: a declaration of this name already exists." -/
#guard_msgs in
#eval typeCheckMessage { decls := [fooCon, fooCon] }

/-- info: "Error in type Foo: a declaration of this name already exists." -/
#guard_msgs in
#eval typeCheckMessage { decls := [fooCon, fooSyn] }

/-- info: "Error in type Foo: a declaration of this name already exists." -/
#guard_msgs in
#eval typeCheckMessage { decls := [fooSyn, fooCon] }

end Strata.ReservedTypeNamesTest
end
