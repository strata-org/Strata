/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.CallElim
meta import Strata.Transform.ProcedureInlining
meta import Strata.Transform.TerminationCheck
meta import Strata.Transform.GenOpaqueTypeParams
meta import Strata.Languages.Core.AbstractCalls
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil

/-! # Program names with reserved prefixes

Type checking and later passes generate types and type variables whose names
start with a reserved prefix (`Lambda.reservedNamePrefixes`). A program may use
such names too: a pass that generates a type name skips the names the program
declares, and type checking renames a function type parameter with a reserved
prefix before it generates type variables. These tests check that no program
name is taken for a generated one.
-/

meta section

/-- The name, type parameters and signature of `f`. -/
def Core.ReservedTypeNamesTest.funcSig (f : Core.Function) : Std.Format :=
  f!"{f.name}<{f.typeArgs}> : {f.inputs.values} → {f.output}"

/-- Print each function (`funcSig`) and the name, type parameters and
    proposition of each lemma that `Core.typeCheck` with quiet options returns,
    or its error message. -/
def Core.ReservedTypeNamesTest.printChecked (p : Core.Program) : IO Unit :=
  match Core.typeCheck .quiet p with
  | .ok p =>
    for d in p.decls do
      match d with
      | .func f _ => IO.println (funcSig f)
      | .lemma l _ => IO.println f!"{l.name}<{l.typeArgs}> : {l.e}"
      | _ => pure ()
  | .error e => IO.println e.message

namespace Strata.ReservedTypeNamesTest

open Core.ReservedTypeNamesTest (funcSig printChecked)
open Core.TestUtil (coreVerdict firstLineOf)

/-! The prefixes the Core passes generate are copied into `Lambda.reservedNamePrefixes`,
which cannot import those passes; these checks keep the copies in sync. -/

#guard Lambda.reservedNamePrefixes.contains Core.CallElim.callElimTyPrefix
#guard Lambda.reservedNamePrefixes.contains Core.ProcedureInlining.inlineTyPrefix
#guard Lambda.reservedNamePrefixes.contains Core.TermCheck.termTyVarPrefix
#guard Lambda.reservedNamePrefixes.contains Core.GenOpaqueTypeParams.freeTyPrefix
#guard Lambda.reservedNamePrefixes.contains Core.abstractTyPrefix

/-! A declared type named like the opaque type that closes a lemma's free type
variable must not be taken for it: the axiom makes that type a singleton, under
which the false lemma would hold. Type checking rejects the lemma, so the
program is never verified. -/

def reservedNamedSingleton :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
function first<a> (xs : MyList a) : a;
function second<a> (xs : MyList a) : a;
type $__free_nil_refl_0;
axiom [single]: forall x : $__free_nil_refl_0, y : $__free_nil_refl_0 :: x == y;
lemma [nil_refl]: first(Nil()) == second(Nil());
#end

-- Type checking rejects the lemma: it is typed at a generated type variable it
-- does not declare.
/--
error: ❌ Type checking error.
Lemma 'nil_refl' is typed at a generated type variable that is not declared
-/
#guard_msgs in
#eval Core.verify reservedNamedSingleton (options := .quiet)

/-! The same program with an unreserved type name gets the same rejection. -/

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
error: ❌ Type checking error.
Lemma 'nil_refl' is typed at a generated type variable that is not declared
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

/-- info: REJECTED: Error in lemma bad: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval coreVerdict (Core.getProgram declaredRigidName).fst

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

/-! Type checking returns `id` with its type parameter renamed to `a` throughout. -/

/-- info: id<[a]> : [a] → a -/
#guard_msgs in
#eval printChecked (Core.getProgram reservedTypeParam).fst

/-! A renamed type parameter also avoids the type variables in scope where
the function is checked: with `a` in scope, `f<$__ty0>` becomes `f<a_1>`. -/

/-- `function f<$__ty0> (x : $__ty0) : $__ty0`, without a body. -/
def reservedIdF : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := ["$__ty0"],
    inputs := [(⟨"x", ()⟩, .ftvar "$__ty0")], output := .ftvar "$__ty0" }

/-- The signature (`funcSig`) of `reservedIdF` checked by `Function.typeCheck`
    in `C` and `Env`, or the error message. -/
def checkedIdF (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) :
    Std.Format :=
  match Core.Function.typeCheck C Env reservedIdF with
  | .ok (f, _) => funcSig f
  | .error e => e

-- `a` is a rigid type variable of the context.
/-- info: f<[a_1]> : [a_1] → a_1 -/
#guard_msgs in
#eval checkedIdF { Core.initTyContext with rigidTypeVars := ["a"] }
  Lambda.TEnv.default

-- `a` is the type of the variable `y` in scope.
/-- info: f<[a_1]> : [a_1] → a_1 -/
#guard_msgs in
#eval checkedIdF Core.initTyContext
  (Lambda.TEnv.default.pushEmptyContext.addInNewestContext
    (T := Core.CoreLParams)
    (Strata.Util.HMap.ofList [(⟨"y", ()⟩, .forAll [] (.ftvar "a"))]))

/-! A procedure or lemma type parameter with a reserved prefix is renamed the same
way. -/

def reservedProcLemmaTypeParam :=
#strata
program Core;
procedure P<$__ty0> (x : $__ty0) {
  assert [refl]: (x == x);
};
lemma [l_refl] <$__ty0> (x : $__ty0): x == x;
#end

/--
info:
Obligation: refl
Property: assert
Result: ✅ pass

Obligation: l_refl
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify reservedProcLemmaTypeParam (options := .quiet)

/-! Type checking returns the lemma `l_refl<$__ty0>` with its type parameter
renamed to `a` throughout. -/

/-- info: l_refl<[a]> : forall x : a :: x == x -/
#guard_msgs in
#eval printChecked
  { decls := [.lemma { name := "l_refl", typeArgs := ["$__ty0"],
                       e := Lambda.LExpr.all Core.coreLoc "x" (some (.ftvar "$__ty0"))
                              (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0)) }
                                  .empty] }

/-! A type with a reserved prefix that a procedure body declares is shown by its
name in a message from the body. -/

def bodyReservedType :=
#strata
program Core;
procedure P<a> (x : a) {
  type $__T;
  var y : $__T;
  y := x;
};
#end

/-- info: REJECTED: Procedure 'P': Rigid type variable 'a' was refined to '$__T' -/
#guard_msgs in
#eval coreVerdict (Core.getProgram bodyReservedType).fst

/-! An undeclared type variable is reported with the type parameters as
written, including one with a reserved prefix. The parser rejects such a
function, so it is built directly, as a front end would. -/

def undeclaredWithReservedParam : Core.Decl :=
  .func { name := ⟨"f", ()⟩, typeArgs := ["$__ty0"],
          inputs := [(⟨"x", ()⟩, .ftvar "$__ty0")], output := .ftvar "a" } .empty

/--
info: REJECTED: Function 'f': type variables [a] appear in the signature but are
not declared in typeArgs [$__ty0]
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict { decls := [undeclaredWithReservedParam] }

/-! The generated types do not stop a program from type checking. Here the
opaque-type pass (which also closes the lemma's free element type of `Nil()` with
a generated type), monomorphization and simplification run first, then type
checking. -/

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
  let phases := Core.preSymbolicEvalPipelinePhases ++ [Core.typeCheckPipelinePhase .quiet]
  match ← (Core.runTransforms p phases).toBaseIO with
  | .ok (p, _) =>
    return toString (p.decls.filterMap fun (d : Core.Decl) =>
      d.getTypeDecl?.map fun (td : Core.TypeDecl) => td.name.name)
  | .error e => return e.message

/-- info: "[MyList, $__free_nil_refl_0, $__opaque_P_a_0]" -/
#guard_msgs in
#eval typeCheckAfterPipeline (Core.getProgram polyProgram).fst

/-! Closing a lemma's free type variable skips a declared type named like the
type that closes it. -/

def declaredFreeName :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
type $__free_nil_refl_0;
lemma [nil_refl]: Nil() == Nil();
#end

/-- info: "[MyList, $__free_nil_refl_0, $__free_nil_refl_0_1]" -/
#guard_msgs in
#eval typeCheckAfterPipeline (Core.getProgram declaredFreeName).fst

/-! A type a procedure body declares with the name of the opaque type that
replaces the procedure's type parameter keeps its name, and the opaque type gets
another one, whether the declaration is in a nested block or in a branch of a
conditional. -/

def blockOpaqueName :=
#strata
program Core;
procedure P<a> (x : a) {
  inner: {
    type $__opaque_P_a_0;
    var y : $__opaque_P_a_0;
    assert [refl]: (x == x);
  }
};
#end

/--
info:
Obligation: refl
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify blockOpaqueName (options := .quiet)

/-- info: "[$__opaque_P_a_1]" -/
#guard_msgs in
#eval typeCheckAfterPipeline (Core.getProgram blockOpaqueName).fst

def iteOpaqueName :=
#strata
program Core;
procedure P<a> (x : a, b : bool) {
  if (b) {
    type $__opaque_P_a_0;
    var y : $__opaque_P_a_0;
    assert [refl]: (x == x);
  }
};
#end

/--
info:
Obligation: refl
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify iteOpaqueName (options := .quiet)

/-- info: "[$__opaque_P_a_1]" -/
#guard_msgs in
#eval typeCheckAfterPipeline (Core.getProgram iteOpaqueName).fst

/-! The same holds for a type a procedure body declares with the name of the
type that closes a lemma's free type variable, as the names after the pipeline
show. -/

def bodyFreeName :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
lemma [nil_refl]: Nil() == Nil();
procedure Q () {
  type $__free_nil_refl_0;
  var z : $__free_nil_refl_0;
  assert [z_refl]: (z == z);
};
#end

/-- info: "[MyList, $__free_nil_refl_0_1]" -/
#guard_msgs in
#eval typeCheckAfterPipeline (Core.getProgram bodyFreeName).fst

/-! A type declared twice is rejected, whatever kinds the two declarations
have. The parser already rejects a source program that does this, so these
programs are built directly, as a front end or a pass would. -/

def fooCon : Core.Decl := .type (.con { name := "Foo", params := [] }) .empty
def fooSyn : Core.Decl := .type (.syn { name := "Foo", typeArgs := [], type := .int }) .empty

/-- info: REJECTED: Error in type Foo: a declaration of this name already exists. -/
#guard_msgs in
#eval coreVerdict { decls := [fooCon, fooCon] }

/-- info: REJECTED: Error in type Foo: a declaration of this name already exists. -/
#guard_msgs in
#eval coreVerdict { decls := [fooCon, fooSyn] }

/-- info: REJECTED: Error in type Foo: a declaration of this name already exists. -/
#guard_msgs in
#eval coreVerdict { decls := [fooSyn, fooCon] }

/-! A rigid type stands for a type parameter while it is checked, and is chosen
to differ from every type name in scope: a synonym named like it does not make
the parameter `int`, for a function or a procedure. -/

def declaredRigidFunc :=
#strata
program Core;
type $__rigid_f_a := int;
function f<a> (x : a) : int { x }
#end

/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval coreVerdict (Core.getProgram declaredRigidFunc).fst

def declaredRigidProc :=
#strata
program Core;
type $__rigid_P_a := int;
procedure P<a> (x : a) {
  assert [z]: (x == 0);
};
#end

/-- info: REJECTED: Procedure 'P': Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval coreVerdict (Core.getProgram declaredRigidProc).fst

/-! A declared type named like a rigid type is a different type from the
parameter, so a body of that type does not have the parameter's type. -/

def declaredRigidOpaque :=
#strata
program Core;
type $__rigid_g_a;
function g<a> (x : a, y : $__rigid_g_a) : a { y }
#end

/-- info: REJECTED: Rigid type variable 'a' was refined to '$__rigid_g_a' -/
#guard_msgs in
#eval coreVerdict (Core.getProgram declaredRigidOpaque).fst

/-! A synonym named like a rigid type is avoided even when declarations of
other kinds come between it and the declaration it would affect. These
programs are built directly as abstract syntax. -/

/-- A synonym of `int` named like the rigid type for parameter `a` of `name`. -/
def rigidAlias (name : String) : Core.Decl :=
  .type (.syn { name := s!"$__rigid_{name}_a", typeArgs := [], type := .int }) .empty

/-- The declaration of an opaque type named `$__rigid_{name}_a`. -/
def rigidDeclared (name : String) : Core.Decl :=
  .type (.con { name := s!"$__rigid_{name}_a", params := [] }) .empty

/-- A function, a datatype and a procedure, none of them polymorphic. -/
def otherDecls : List Core.Decl :=
  [.func { name := ⟨"g", ()⟩, inputs := [(⟨"y", ()⟩, .int)],
           output := .int } .empty,
   .type (.data [{ name := "MyUnit", typeArgs := [],
                   constrs := [{ name := ⟨"MkU", ()⟩, args := [] }],
                   constrs_ne := rfl }]) .empty,
   .proc { header := { name := ⟨"Q", ()⟩, typeArgs := [], inputs := [],
                       outputs := [] },
           spec := { preconditions := [], postconditions := [] },
           body := .structured [] false } .empty]

/-- `function f<a> (x : a) : int { x }`, recursive when `isRecursive`. -/
def rigidF (isRecursive : Bool) : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := ["a"], isRecursive,
    inputs := [(⟨"x", ()⟩, .ftvar "a")], output := .int,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none) }

-- A synonym `$__rigid_f_a` before other declarations does not make `a` `int`.
/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval coreVerdict
  { decls := rigidAlias "f" :: otherDecls ++ [.func (rigidF false) .empty] }

-- The same holds for `f` in a recursive function block.
/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval coreVerdict
  { decls := rigidAlias "f" :: otherDecls ++ [.recFuncBlock [rigidF true] .empty] }

-- The same holds for a lemma `bad<a>`.
/-- info: REJECTED: Error in lemma bad: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval coreVerdict
  { decls := rigidAlias "bad" :: otherDecls ++
      [.lemma { name := "bad", typeArgs := ["a"],
                e := Lambda.LExpr.all Core.coreLoc "x" (some (.ftvar "a"))
                       (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.intConst Core.coreLoc 0)) }
                           .empty] }

/-! A rigid type also avoids the type names its own declaration writes, so
such a name stays an unregistered type, or the type the body declares. -/

/-- The type `$__rigid_P_a`, named like the rigid type for `a` of `P`. -/
def rigidPA : Lambda.LMonoTy := .tcons "$__rigid_P_a" []

-- A function body annotated `$__rigid_f_a` is not taken for the type of `a`.
/--
info: REJECTED: Type $__rigid_f_a is not an instance of a previously registered type!
-/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  { decls := [.func { rigidF false with
      output := .ftvar "a",
      body := some (.fvar Core.coreLoc ⟨"x", ()⟩ (some (.tcons "$__rigid_f_a" []))) }
    .empty] }

/-- `procedure P<a> (x : a)` with no conditions and an empty body. -/
def rigidP : Core.Procedure :=
  { header := { name := ⟨"P", ()⟩, typeArgs := ["a"],
                inputs := [(⟨"x", ()⟩, .ftvar "a")], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] false }

-- A type `$__rigid_P_a` the body declares differs from the rigid type of `a`.
/-- info: REJECTED: Procedure 'P': Rigid type variable 'a' was refined to '$__rigid_P_a' -/
#guard_msgs in
#eval coreVerdict
  { decls := [.proc { rigidP with
      body := .structured [
        .typeDecl { name := "$__rigid_P_a", params := [] } .empty,
        Core.Statement.init ⟨"y", ()⟩ (.forAll [] rigidPA) .nondet .empty,
        Core.Statement.set ⟨"y", ()⟩ (.fvar Core.coreLoc ⟨"x", ()⟩ none) .empty] false }
      .empty] }

-- A type `$__rigid_P_a` the body declares is not taken for the rigid type of
-- `a`.
/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict
  { decls := [.proc { rigidP with
      body := .structured
        [.typeDecl { name := "$__rigid_P_a", params := [] } .empty] false }
      .empty] }

-- A precondition annotated `$__rigid_P_a` is not taken for the type of `a`.
/--
info: REJECTED: Procedure 'P', condition 'p': Type $__rigid_P_a is not an
instance of a previously registered type!
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [.proc { rigidP with
      spec := { preconditions := [("p",
                  ⟨.eq Core.coreLoc (.fvar Core.coreLoc ⟨"x", ()⟩ (some rigidPA))
                     (.fvar Core.coreLoc ⟨"x", ()⟩ none), .Default, #[]⟩)],
                postconditions := [] } } .empty] }

-- A lemma binder annotated `$__rigid_bad_a` is not taken for the type of `a`.
/--
info: REJECTED: Error in lemma bad: Type $__rigid_bad_a is not an instance of a
previously registered type!
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [.lemma { name := "bad", typeArgs := ["a"],
                       e := Lambda.LExpr.all Core.coreLoc "x" (some (.ftvar "a"))
                              (.all Core.coreLoc "y" (some (.tcons "$__rigid_bad_a" []))
                                (.eq Core.coreLoc (.bvar Core.coreLoc 1) (.bvar Core.coreLoc 0))) }
                                    .empty] }

-- A map literal over the sort `$__rigid_f_a` is not taken for a map over the
-- type of `a`.
/--
info: REJECTED: The type (Map $__rigid_f_a int) of the literal {_ ↦ 0} uses a
type constructor that is not registered in the known types.
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [.func { rigidF false with
      inputs := [], output := .tcons "Map" [.ftvar "a", .int],
      body := some (.const Core.coreLoc
        (.mapConst (Lambda.LSort.tcons "$__rigid_f_a" []) Lambda.LSort.int
          (Lambda.LConst.intConst 0) #[])) }
    .empty] }

/-- The map literal `{_ ↦ 0}` whose key sort is `$__rigid_{name}_a`. -/
def rigidLit (name : String) : Core.Expression.Expr :=
  .const Core.coreLoc (.mapConst (Lambda.LSort.tcons s!"$__rigid_{name}_a" [])
    Lambda.LSort.int (Lambda.LConst.intConst 0) #[])

/-- The proposition `{_ ↦ 0} == {_ ↦ 0}` over `rigidLit name`. -/
def rigidLitProp (name : String) : Core.Expression.Expr :=
  .eq Core.coreLoc (rigidLit name) (rigidLit name)

-- A literal over an undeclared rigid-looking sort is rejected.
/--
info: REJECTED: Procedure 'P', condition 'p': The type (Map $__rigid_P_a int)
of the literal {_ ↦ 0} uses a type constructor that is not registered in the
known types.
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [.proc { rigidP with
      spec := { preconditions := [("p", ⟨rigidLitProp "P", .Default, #[]⟩)],
                postconditions := [] } } .empty] }

-- A literal over an undeclared rigid-looking sort is rejected in a body.
/--
info: REJECTED: Procedure 'P': The type (Map $__rigid_P_a int) of the literal {_ ↦ 0} uses a
type constructor that is not registered in the known types.
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [.proc { rigidP with
      body := .structured
        [Core.Statement.assert "a" (rigidLitProp "P") .empty] false }
    .empty] }

-- A literal over an undeclared rigid-looking sort is rejected in a lemma.
/--
info: REJECTED: Error in lemma l: The type (Map $__rigid_l_a int) of the
literal {_ ↦ 0} uses a type constructor that is not
registered in the known types.
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [.lemma { name := "l", typeArgs := ["a"],
                       e := rigidLitProp "l" } .empty] }

-- A declared literal sort is accepted: the rigid type avoids its name.
/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict
  { decls := [rigidDeclared "P",
    .proc { rigidP with
      spec := { preconditions := [("p", ⟨rigidLitProp "P", .Default, #[]⟩)],
                postconditions := [] } } .empty] }

-- The same holds for a literal in an assertion of the body.
/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict
  { decls := [rigidDeclared "P",
    .proc { rigidP with
      body := .structured
        [Core.Statement.assert "a" (rigidLitProp "P") .empty] false }
    .empty] }

-- The same holds for a literal in a lemma.
/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict
  { decls := [rigidDeclared "l",
    .lemma { name := "l", typeArgs := ["a"], e := rigidLitProp "l" } .empty] }

/-- The type `Map a int` over the type parameter `a`. -/
def mapAInt : Lambda.LMonoTy := .tcons "Map" [.ftvar "a", .int]

/-- `rigidP` with the input `m : Map a int` and no other change. -/
def rigidPMap : Core.Procedure :=
  { rigidP with
    header := { rigidP.header with inputs := [(⟨"m", ()⟩, mapAInt)] } }

-- A declared sort named like the rigid type is not the type of `a`.
/--
info: REJECTED: Procedure 'P', condition 'p': Rigid type variable 'a' was
refined to '$__rigid_P_a'
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [rigidDeclared "P",
    .proc { rigidPMap with
      spec := { preconditions :=
                  [("p", ⟨.eq Core.coreLoc (.fvar Core.coreLoc ⟨"m", ()⟩ none) (rigidLit "P"),
                    .Default, #[]⟩)],
                postconditions := [] } } .empty] }

-- The same holds for an assertion of the body.
/-- info: REJECTED: Procedure 'P': Rigid type variable 'a' was refined to '$__rigid_P_a' -/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [rigidDeclared "P",
    .proc { rigidPMap with
      body := .structured [Core.Statement.assert "a"
        (.eq Core.coreLoc (.fvar Core.coreLoc ⟨"m", ()⟩ none) (rigidLit "P")) .empty] false }
    .empty] }

-- The same holds for a lemma over a map bound at the type of `a`.
/--
info: REJECTED: Error in lemma l: Rigid type variable 'a' was refined to
'$__rigid_l_a'
-/
#guard_msgs (whitespace := lax) in
#eval firstLineOf <| coreVerdict
  { decls := [rigidDeclared "l",
    .lemma { name := "l", typeArgs := ["a"],
             e := .all Core.coreLoc "m" (some mapAInt)
                    (.eq Core.coreLoc (.bvar Core.coreLoc 0) (rigidLit "l")) } .empty] }

/-! A type named like the rigid type for a lemma's type parameter is not taken for it, whether
it is declared before or after the lemma: the lemma keeps its own parameter `a`. -/

/-- `lemma [L] <a>: (forall x : a, y : a :: x == y) ==> (forall u : a, v : a :: u == v)`. -/
def oneTypeLemma : Core.Decl :=
  match (Core.getProgram
    #strata
    program Core;
    lemma [L] <a>: (forall x : a, y : a :: x == y) ==> (forall u : a, v : a :: u == v);
    #end).fst.decls with
  | [d] => d
  | _ => .type (.con { name := "unexpected", params := [] }) .empty

/-- The program `Core.typeCheck` returns for `p`, or its error message. -/
def printProgram (p : Core.Program) : IO Unit :=
  match _root_.Core.typeCheck .quiet p with
  | .ok q => IO.println (toString (Std.format q))
  | .error e => IO.println s!"error: {e.message}"

/--
info: program Core;

type $__rigid_L_a;
lemma [L] <a>: (forall x : a :: forall y : a :: x == y) ==> (forall u : a :: forall v : a :: u == v);
-/
#guard_msgs in
#eval printProgram { decls := [rigidDeclared "L", oneTypeLemma] }

/--
info: program Core;

lemma [L] <a>: (forall x : a :: forall y : a :: x == y) ==> (forall u : a :: forall v : a :: u == v);
type $__rigid_L_a;
-/
#guard_msgs in
#eval printProgram { decls := [oneTypeLemma, rigidDeclared "L"] }

/-! The verdict shows it too. A one-value datatype named like the rigid type for `a` would make
`forall x : a, y : a :: x == y` hold if it were taken for `a`; the lemma stays unproved at an
arbitrary `a`, whether the datatype is declared before or after it. -/

def singletonBeforeLemma :=
#strata
program Core;
datatype $__rigid_L_a () { C() };
lemma [L] <a>: forall x : a, y : a :: x == y;
#end

/--
info:
Obligation: L
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify singletonBeforeLemma (options := .quiet)

def singletonAfterLemma :=
#strata
program Core;
lemma [L] <a>: forall x : a, y : a :: x == y;
datatype $__rigid_L_a () { C() };
#end

/--
info:
Obligation: L
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify singletonAfterLemma (options := .quiet)

/-! Rigid type names are built from a lemma's label and type parameters, which a front end may
write with `#` (the parser accepts no `#` there, so these lemmas are built directly). Two type
parameters whose names differ only by `#` and `_` (`Lb`), and two lemmas whose labels differ so
(`L#a`, `L_a`), still each keep their own types. These outputs depend on how rigid names are built
from names that contain `#`; a change to that naming, such as escaping `#` instead of replacing
it, may change them. -/

/-- `oneTypeLemma` labeled `name`. -/
def oneTypeLemmaNamed (name : String) : Core.Decl :=
  match oneTypeLemma with
  | .lemma l md => .lemma { l with name := name } md
  | d => d

/-- `lemma [Lb] <x#y, x_y>: (forall p : x#y, q : x_y :: p == p && q == q)`, from a parsed
    `<x, y>` lemma with its type parameters renamed. -/
def hashTyParamsLemma : Core.Decl :=
  match (Core.getProgram
    #strata
    program Core;
    lemma [Lb] <x, y>: (forall p : x, q : y :: p == p && q == q);
    #end).fst.decls with
  | [.lemma l md] =>
    let S : Lambda.Subst :=
      Strata.Util.HMaps.ofScopes [[("x", .ftvar "x#y"), ("y", .ftvar "x_y")]]
    .lemma { l with typeArgs := ["x#y", "x_y"], e := l.e.applyTypeSubst S } md
  | _ => .type (.con { name := "unexpected", params := [] }) .empty

/-- The program the type checker, `Core.Program.typeCheck`, returns for `p`. -/
def printCheckerOutput (p : Core.Program) : IO Unit :=
  let C := { Lambda.LContext.default with
                functions := _root_.Core.Factory, knownTypes := _root_.Core.KnownTypes }
  match _root_.Core.Program.typeCheck C Lambda.TEnv.default p with
  | .ok (q, _) => IO.println (toString (Std.format q))
  | .error e => IO.println s!"error: {e.message}"

/--
info: program Core;

lemma [|L#a|] <a>: (forall x : a :: forall y : a :: x == y) ==> (forall u : a :: forall v : a :: u == v);
lemma [Lb] <|x#y|, x_y>(p : |x#y|, q : x_y): p == p && q == q;
lemma [L_a] <a>: (forall x : a :: forall y : a :: x == y) ==> (forall u : a :: forall v : a :: u == v);
-/
#guard_msgs in
#eval printCheckerOutput
  { decls := [oneTypeLemmaNamed "L#a", hashTyParamsLemma, oneTypeLemmaNamed "L_a"] }

-- `Core.typeCheck` accepts `Lb`, whose label has no `#`, with its two type parameters apart.
/--
info: program Core;

lemma [Lb] <|x#y|, x_y>(p : |x#y|, q : x_y): p == p && q == q;
-/
#guard_msgs in
#eval printProgram { decls := [hashTyParamsLemma] }

/-! A supplied factory is used as given, so a function in it whose type
parameter has a reserved prefix is rejected. -/

/-- `base` with the function `f` added, or `base` if `f` cannot be added. -/
def factoryWith (base : Lambda.Factory Core.CoreLParams) (f : Core.Function) :
    Lambda.Factory Core.CoreLParams :=
  match base.tryPush f.toLFunc with
  | .ok fac => fac
  | .error _ => base

/-- The default factory with the function `idf<$__ty0>` added. -/
def reservedFactory : Lambda.Factory Core.CoreLParams :=
  factoryWith Lambda.Factory.default
    { name := ⟨"idf", ()⟩, typeArgs := ["$__ty0"],
      inputs := [(⟨"x", ()⟩, .ftvar "$__ty0")], output := .ftvar "$__ty0" }

/-- info: REJECTED: Factory function 'idf': type parameter '$__ty0' is a reserved name -/
#guard_msgs in
#eval coreVerdict { decls := [] } (factory := some reservedFactory)

/-! The rigid type names chosen for the type parameters of a procedure `P`. -/

/-- The checking context with `names` registered as nullary types. -/
def contextKnowing (names : List String) : Core.Expression.TyContext :=
  { Core.initTyContext with
    knownTypes := names.foldl (fun ks n => ks.insert n 0)
      Core.initTyContext.knownTypes }

/-- The rigid names for the type parameters `typeArgs` of a definition named
    `P` that mentions no type names, checked in `C` and `Env`. -/
def rigidNamesOfP (C : Core.Expression.TyContext) (typeArgs : List String)
    (Env : Core.Expression.TyEnv := Lambda.TEnv.default) : Core.RigidNames :=
  Core.rigidNamesAvoiding C (Core.scopeTyNameThunk C Env) (Thunk.pure ∅) "P" (fun _ => [])
    typeArgs

-- A registered `$__rigid_P_a` makes `a` take the next variant.
/-- info: [("a", "$__rigid_P_a_1")] -/
#guard_msgs in
#eval rigidNamesOfP (contextKnowing ["$__rigid_P_a"]) ["a"]

-- A registered `$__rigid_P_a_1` as well makes `a` take the one after.
/-- info: [("a", "$__rigid_P_a_2")] -/
#guard_msgs in
#eval rigidNamesOfP (contextKnowing ["$__rigid_P_a", "$__rigid_P_a_1"]) ["a"]

-- Each parameter's name also differs from the names chosen before it.
/-- info: [("a", "$__rigid_P_a_1"), ("a_1", "$__rigid_P_a_1_1")] -/
#guard_msgs in
#eval rigidNamesOfP (contextKnowing ["$__rigid_P_a"]) ["a", "a_1"]

-- A declaration without type parameters gets no rigid names.
/-- info: [] -/
#guard_msgs in
#eval rigidNamesOfP (contextKnowing ["$__rigid_P_a"]) []

-- A type name in a factory signature is avoided even when it is not registered.
/-- info: [("a", "$__rigid_P_a_1")] -/
#guard_msgs in
#eval rigidNamesOfP { Core.initTyContext with
  functions := factoryWith Core.Factory
    { name := ⟨"h", ()⟩, inputs := [(⟨"x", ()⟩, rigidPA)], output := .int } }
  ["a"]

-- The same holds for the output type of a factory function.
/-- info: [("a", "$__rigid_P_a_1")] -/
#guard_msgs in
#eval rigidNamesOfP { Core.initTyContext with
  functions := factoryWith Core.Factory
    { name := ⟨"h", ()⟩, inputs := [], output := rigidPA } }
  ["a"]

-- The type of a variable in scope is avoided.
/-- info: [("a", "$__rigid_P_a_1")] -/
#guard_msgs in
#eval rigidNamesOfP Core.initTyContext ["a"]
  (Lambda.TEnv.default.pushEmptyContext.addInNewestContext
    (T := Core.CoreLParams)
    (Strata.Util.HMap.ofList [(⟨"y", ()⟩, .forAll [] rigidPA)]))

-- The body of a type synonym in scope is avoided.
/-- info: [("a", "$__rigid_P_a_1")] -/
#guard_msgs in
#eval rigidNamesOfP Core.initTyContext ["a"]
  (Lambda.TEnv.default.updateContext { Lambda.TEnv.default.context with
    aliases := [{ name := "S", typeArgs := [], type := rigidPA }] })

end Strata.ReservedTypeNamesTest

end
