/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementType
meta import StrataTest.Languages.Core.Tests.TestUtil
meta import StrataDDM.Integration.Lean.HashCommands
import all Strata.Languages.Core.StatementType

meta section

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)

open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: ok: {
  var x : int := xinit;
  x := xinit;
  var y : int := xinit;
}
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default
                   (TEnv.default.updateContext
                     { types := Strata.Util.HMaps.ofScopes [[("xinit", t[int])]] })
                   Program.init
                   none
                   [.init "x" t[int] (.det eb[xinit]) .empty,
                    .set "x" eb[xinit] .empty,
                    .init "y" t[int] (.det eb[xinit]) .empty]
         return format ans.fst


/-- info: error: Variable x of type bool already in context. -/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default
                   (TEnv.default.updateContext
                     { types := Strata.Util.HMaps.ofScopes [[("x", t[bool])]] })
                   Program.init
                   none
                   [
                    .init "x" t[bool] (.det eb[#true]) .empty
                   ]
         return format ans

/--
info: ok: context:
types:   [(x, int) (y, int) (zinit, bool)]
aliases: []
state:
tyGen: 0
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst:
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default
                   (TEnv.default.updateContext
                     { types := Strata.Util.HMaps.ofScopes [[("zinit", t[bool])]] })
                    Program.init
                    none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .init "y" t[int] (.det eb[#6]) .empty,
                    .block "label_0"

                      [Statement.init "z" t[bool] (.det eb[zinit]) .empty,
                       Statement.assume "z_false" eb[z == #false] .empty,

                      .ite (.det eb[z == #false])
                        [Statement.set "x" eb[y] .empty]
                        [Statement.assert "trivial" eb[#true] .empty]
                        .empty,

                      Statement.assert "x_eq_y_label_0" eb[x == y] .empty,
                      ]
                      .empty,
                    .assert "x_eq_y" eb[x == y] .empty
                    ]
          return format ans.snd

/-- info: error: Impossible to unify bool with int. -/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .init "y" t[int] (.det eb[#6]) .empty,
                    .init "z" t[bool] (.det eb[if (x == y) then #true else #2]) .empty
                    ]
          return format ans

/-- info: error: Variable x of type bool already in context. -/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[bool] (.det eb[#true]) .empty,
                    .block "label_0"
                      [ Statement.init "x" t[int] (.det eb[#1]) .empty ]
                      .empty
                    ]
          return format ans

/--
info: ok: context:
types:   [(x, int)]
aliases: []
state:
tyGen: 0
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst:
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .ite (.det eb[x == #3])
                    [
                      Statement.init "y" t[int] (.det eb[x]) .empty,
                      Statement.assert "local_y_eq_3" eb[y == #3] .empty
                    ]
                    [ Statement.init "z" t[bool] (.det eb[#true]) .empty ]
                    .empty
                    ]
          return format ans.snd

/--
info: ok: {
  var x : int := 1;
  x := 2;
}
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
              [
              .init "x" t[int] (.det eb[#1]) .empty,
              .set "x" eb[#2] .empty
              ]
          return (format ans.fst)

-- A `var` declared at a polymorphic type is rejected.
/--
info: error: Local variable declaration has type ∀[α]. α. Polymorphic variable declarations are not allowed.
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default
                      (TEnv.default.updateContext
                        { types := Strata.Util.HMaps.ofScopes [[("xinit", t[int])]] })
                      Program.init none
              [.init "y" t[∀α. %α] (.det eb[xinit]) .empty]
          return (format ans.fst)

-- A `var` type may have free type variables; here `a` is solved to `int` and `b` to `bool → int`.
/--
info: ok: {
  var m1 : int -> int := fn;
  var m2 : (bool -> int) -> int := fun __q0 : (bool -> int) => __q0(fn(true));
}
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default
                   (TEnv.default.updateContext
                     { types := Strata.Util.HMaps.ofScopes [[("fn", t[∀a. %a → %a])]] })
                      Program.init none
              [
              .init "m1" t[%a → int] (.det eb[fn]) .empty,
              .init "m2" t[%b → int] (.det eb[(λ (%0 (fn #true)))]) .empty
              ]
          return (format ans.fst)

-- A block label ending in `_<digits>` is accepted.
/--
info: ok: {
  label_0 : {}
}
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
              [.block "label_0" [] .empty]
          return (format ans.fst)

-- Two sibling blocks may each declare the same type name.
/--
info: ok: {
  b1 :
  {
    type MyT (arity 0)
  }
  b2 :
  {
    type MyT (arity 0)
  }
}
-/
#guard_msgs in
#eval do
  let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
    [ .block "b1" [ .typeDecl { name := "MyT", params := [] } .empty ] .empty,
      .block "b2" [ .typeDecl { name := "MyT", params := [] } .empty ] .empty ]
  return format ans.fst

-- A local variable with a reserved name is accepted.
/--
info: ok: ({
   var $__ty0 : int := 0;
 },
 context:
 types:   [($__ty0, int)]
 aliases: [] state: tyGen: 0 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: )
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                   [.init "$__ty0" t[int] (.det eb[#0]) .empty]
         return format ans

-- An assertion with a reserved label is accepted.
/--
info: ok: ({
   assert [$__ty0]: true;
 },
 context:
 types:   []
 aliases: [] state: tyGen: 0 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: )
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                   [.assert "$__ty0" eb[#true] .empty]
         return format ans

-- A block with a reserved label is accepted.
/--
info: ok: ({
   $__ty0 : {}
 },
 context:
 types:   
 aliases: [] state: tyGen: 0 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: )
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                   [.block "$__ty0" [] .empty]
         return format ans

-- A loop invariant with a reserved label is accepted.
/--
info: ok: ({
   while * (none) [[$__ty0]: true] {}
 },
 context:
 types:   []
 aliases: [] state: tyGen: 0 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: )
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                   [.loop .nondet none [("$__ty0", eb[#true])] [] .empty]
         return format ans

end Tests

/-! ## A body-local type is in scope only after its declaration, within its block

A variable's stored type may name only types in scope at the variable. -/

section BodyLocalTypeDeclScopeTests
open Std (Format)
open Core.TestUtil (declNondet firstLineVerdict stmtEnv var)
open Lambda

/-- The identity function applied to `y`. -/
private def idAppY : Core.Expression.Expr :=
  LExpr.app Core.coreLoc (LExpr.abs Core.coreLoc "z" none (LExpr.bvar Core.coreLoc 0))
      (LExpr.fvar Core.coreLoc "y" none)

/-- `y` at a type variable, then type `MyT`, then `x : MyT`, and an assertion `y = x` that solves
    `y`'s type to `MyT`, which is not in scope where `y` is declared. -/
private def typeDeclAfterUseStmts : List Statement :=
  [ Statement.init "y" (.forAll [] (.ftvar "a")) .nondet .empty,
    .typeDecl { name := "MyT", params := [] } .empty,
    Statement.init "x" (.forAll [] (.tcons "MyT" [])) .nondet .empty,
    Statement.assert "a1" (LExpr.eq Core.coreLoc idAppY (LExpr.fvar Core.coreLoc "x" none)) .empty ]

/-- Type `MyT`, then `x : MyT`. -/
private def typeDeclBeforeUseStmts : List Statement :=
  [ .typeDecl { name := "MyT", params := [] } .empty,
    Statement.init "x" (.forAll [] (.tcons "MyT" [])) .nondet .empty ]

/-- A type declared in a block, then a variable of that type after the block. -/
private def typeDeclEscapingBlockStmts : List Statement :=
  [ .block "b" [ .typeDecl { name := "LocalOnly", params := [] } .empty ] .empty,
    Statement.init "x" (.forAll [] (.tcons "LocalOnly" [])) .nondet .empty ]

mutual
/-- The declared types in `s`; nested lists in brackets, conditional branches split by `|`. -/
private def stmtDeclTys : Statement → List Format
  | .cmd (.cmd (.init x (.forAll _ ty) _ _)) => [f!"{x.name} : {ty}"]
  | .block _ b _ | .loop _ _ _ b _ => [f!"[{Format.joinSep (stmtsDeclTys b) ", "}]"]
  | .ite _ t e _ =>
    [f!"[{Format.joinSep (stmtsDeclTys t) ", "} | {Format.joinSep (stmtsDeclTys e) ", "}]"]
  | _ => []

/-- List form of `stmtDeclTys`. -/
private def stmtsDeclTys : List Statement → List Format
  | [] => []
  | s :: ss => stmtDeclTys s ++ stmtsDeclTys ss
end

/-- The statement checker's error on `ss`, or the declared types of its output as in
    `stmtsDeclTys`. -/
private def stmtScopedVerdict (ss : List Statement) : Format :=
  match Statement.typeCheck initTyContext stmtEnv Program.init none ss with
  | .error e => Std.format e
  | .ok (ss', _) => f!"ok, declared types: {Format.joinSep (stmtsDeclTys ss') ", "}"

/-- The statement checker's verdict on `ss`, with the first line of any diagnostic. -/
private def stmtFirstLine (ss : List Statement) : Format :=
  firstLineVerdict (Statement.typeCheck initTyContext stmtEnv Program.init none ss)

/--
info: Variable `y` has type `MyT`, which is not declared where `y` is declared. A `type`
declaration inside a body is in scope for the statements that follow it, and only within its own
block.
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict typeDeclAfterUseStmts

/--
info: ok, declared types: x : MyT
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict typeDeclBeforeUseStmts

/-- `y` at `a → int`, then type `MyT` and `x : MyT → int`, and an assertion `y = x` that solves
    `y`'s type to one using `MyT`, which is not in scope where `y` is declared. -/
private def typeDeclAfterUseArrowStmts : List Statement :=
  [ Statement.init "y" (.forAll [] (.tcons "arrow" [.ftvar "a", .tcons "int" []])) .nondet
      .empty,
    .typeDecl { name := "MyT", params := [] } .empty,
    Statement.init "x" (.forAll [] (.tcons "arrow" [.tcons "MyT" [], .tcons "int" []])) .nondet
      .empty,
    Statement.assert "a1" (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "y" none)
                           (LExpr.fvar Core.coreLoc "x" none)) .empty ]

/-- As `typeDeclAfterUseArrowStmts`, with `y`'s type solved to one using two later types. -/
private def typeDeclAfterUseTwoStmts : List Statement :=
  [ Statement.init "y" (.forAll [] (.tcons "arrow" [.ftvar "a", .ftvar "b"])) .nondet .empty,
    .typeDecl { name := "MyT", params := [] } .empty,
    .typeDecl { name := "MyU", params := [] } .empty,
    Statement.init "x" (.forAll [] (.tcons "arrow" [.tcons "MyT" [], .tcons "MyU" []])) .nondet
      .empty,
    Statement.assert "a1" (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "y" none)
                           (LExpr.fvar Core.coreLoc "x" none)) .empty ]

/--
info: Variable `y` has type `(arrow MyT int)`, which uses `MyT`, but that type is not declared
where `y` is declared. A `type` declaration inside a body is in scope for the statements that
follow it, and only within its own block.
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict typeDeclAfterUseArrowStmts

/--
info: Variable `y` has type `(arrow MyT MyU)`, which uses `MyT`, `MyU`, but those types are not
declared where `y` is declared. A `type` declaration inside a body is in scope for the statements
that follow it, and only within its own block.
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict typeDeclAfterUseTwoStmts

-- A declaration after the block cannot use the block's type.
/--
info: REJECTED: Type LocalOnly is not an instance of a previously registered type!
-/
#guard_msgs (whitespace := lax) in
#eval stmtFirstLine typeDeclEscapingBlockStmts

/-! ## Written type variables are scoped by block

A written type variable's binding ends with its enclosing block, branch or loop body. -/

/-- A program with one procedure `P` with type parameters `typeArgs`, inputs `inputs` and body
    `ss`. -/
private def bodyPgm (ss : List Statement) (typeArgs : List TyIdentifier := [])
    (inputs : @LMonoTySignature Unit := []) : Program := { decls := [
  .proc { header := { name := "P", typeArgs, inputs, outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured ss } .empty ]}

/-- The procedure checker's error on body `ss`, or the declared types of the elaborated body. -/
private def procVerdict (ss : List Statement) : Format :=
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default (bodyPgm ss) with
  | .error e => Std.format e
  | .ok (p, _) =>
    match p.decls with
    | [.proc pr _] =>
      match pr.body with
      | .structured b => f!"ok, declared types: {Format.joinSep (stmtsDeclTys b) ", "}"
      | .cfg _ => "unexpected control-flow-graph body"
    | _ => "unexpected declarations"

/-- Declares `T` and solves the type variable `b` to `T` through `y`. -/
private def solveToTStmts : List Statement :=
  [ .typeDecl { name := "T", params := [] } .empty,
    Statement.init "x" (.forAll [] (.tcons "T" [])) .nondet .empty,
    Statement.init "y" (.forAll [] (.ftvar "b")) (.det (LExpr.fvar Core.coreLoc "x" none)) .empty ]

/-- `solveToTStmts` as a block. -/
private def blockSolvingTyVarStmts : List Statement :=
  [ .block "blk" solveToTStmts .empty ]

/-- `blockSolvingTyVarStmts`, then a variable at `b` initialized with an integer; this `b` is not
    the block's. -/
private def tyVarSolvedInBlockThenUsedStmts : List Statement :=
  blockSolvingTyVarStmts ++
    [ Statement.init "escaped" (.forAll [] (.ftvar "b")) (.det (LExpr.intConst Core.coreLoc 1))
      .empty ]

/-- A variable at `b` declared before a block, assigned a `T` in the block and an integer after
    it; the two assignments conflict. -/
private def assignAfterBlockStmts : List Statement :=
  [ Statement.init "y" (.forAll [] (.ftvar "b")) .nondet .empty,
    .block "blk" [
      .typeDecl { name := "T", params := [] } .empty,
      Statement.init "x" (.forAll [] (.tcons "T" [])) .nondet .empty,
      Statement.set "y" (LExpr.fvar Core.coreLoc "x" none) .empty
    ] .empty,
    Statement.set "y" (LExpr.intConst Core.coreLoc 1) .empty ]

/-- Two sibling blocks, each declaring its own `T` and solving its own `b` to it. -/
private def siblingBlocksSolvingTyVarStmts : List Statement :=
  [ .block "b1" solveToTStmts .empty,
    .block "b2" solveToTStmts .empty ]

/-- Declares `T`, solves `b` to `T` in an inner block, then declares `z` at a `b` of its own. -/
private def outerTypeInnerSolveBody : List Statement :=
  [ .typeDecl { name := "T", params := [] } .empty,
    .block "inner" [
      Statement.init "x" (.forAll [] (.tcons "T" [])) .nondet .empty,
      Statement.init "y" (.forAll [] (.ftvar "b")) (.det (LExpr.fvar Core.coreLoc "x" none)) .empty
    ] .empty,
    Statement.init "z" (.forAll [] (.ftvar "b")) .nondet .empty ]

/-- `outerTypeInnerSolveBody` wrapped in an outer block. -/
private def outerTypeInnerSolveStmts : List Statement :=
  [ .block "outer" outerTypeInnerSolveBody .empty ]

/-- An inner block declares `T` and solves its `b` to it, inside an outer block that then
    declares a variable at a `b` of its own, initialized with an integer. -/
private def innerTypeInnerSolveStmts : List Statement :=
  [ .block "outer" [
      .block "inner" solveToTStmts .empty,
      Statement.init "z" (.forAll [] (.ftvar "b")) (.det (LExpr.intConst Core.coreLoc 1)) .empty
    ] .empty ]

/-- A block solving its `b` to `int`, followed by a declaration at a `b` of its own initialized
    with an integer. -/
private def blockSolvingTyVarToIntStmts : List Statement :=
  [ .block "blk" [
      Statement.init "y" (.forAll [] (.ftvar "b")) (.det (LExpr.intConst Core.coreLoc 1)) .empty
    ] .empty,
    Statement.init "after" (.forAll [] (.ftvar "b")) (.det (LExpr.intConst Core.coreLoc 2)) .empty ]

/-- An `if` whose then-branch declares `T` and solves its `b` to it. -/
private def iteBranchSolvingTyVarStmts : List Statement :=
  [ .ite .nondet solveToTStmts [] .empty ]

/-- A block declaring `x : T` and passing `x` to an unannotated lambda, whose parameter type may
    be solved to `T`. -/
private def blockTypeOnlyGeneratedStmts : List Statement :=
  [ .block "blk" [
      .typeDecl { name := "T", params := [] } .empty,
      Statement.init "x" (.forAll [] (.tcons "T" [])) .nondet .empty,
      Statement.assert "a"
        (LExpr.app Core.coreLoc (LExpr.abs Core.coreLoc "z" none
                                 (LExpr.eq Core.coreLoc (LExpr.bvar Core.coreLoc 0)
                                   (LExpr.bvar Core.coreLoc 0)))
          (LExpr.fvar Core.coreLoc "x" none)) .empty
    ] .empty ]

/--
info: ok, declared types: [x : T, y : T]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict blockSolvingTyVarStmts

/--
info: ok, declared types: [x : T, y : T], escaped : int
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict tyVarSolvedInBlockThenUsedStmts

/--
info: Procedure 'P': Impossible to unify b with int.
First mismatch: T with int.
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict assignAfterBlockStmts

/--
info: ok, declared types: [x : T, y : T], [x : T, y : T]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict siblingBlocksSolvingTyVarStmts

/--
info: ok, declared types: [x : T, y : T], z : b_1
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerTypeInnerSolveBody

/--
info: ok, declared types: [[x : T, y : T], z : b_1]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerTypeInnerSolveStmts

/--
info: ok, declared types: [[x : T, y : T], z : int]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict innerTypeInnerSolveStmts

/--
info: ok, declared types: [y : int], after : int
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict blockSolvingTyVarToIntStmts

/--
info: ok, declared types: [x : T, y : T | ]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict iteBranchSolvingTyVarStmts

/--
info: ok, declared types: [x : T]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict blockTypeOnlyGeneratedStmts

/-! ### More cases for the scoping of written type variables -/

private def tyT : TypeConstructor := { name := "T", params := [] }

private def tyU : TypeConstructor := { name := "U", params := [] }

/-- `var x : ty := e`. -/
private def declInit (x : String) (ty : LMonoTy) (e : Expression.Expr) : Statement :=
  Statement.init x (.forAll [] ty) (.det e) .empty

/-- The written type variable `b`. -/
private def tyB : LMonoTy := .ftvar "b"

/-- Sibling blocks solving their own `b` to their own block-local types `T` and `U`. -/
private def siblingTypesStmts : List Statement :=
  [ .block "b1" [.typeDecl tyT .empty, declNondet "x" (.tcons "T" []), declInit "y" tyB (var "x")]
      .empty,
    .block "b2" [.typeDecl tyU .empty, declNondet "x" (.tcons "U" []), declInit "y" tyB (var "x")]
      .empty ]

/-- A block solving its `b` to its `T`, then a new `T` after the block and a `b` of its own
    solved to that `T`. -/
private def redeclaredTypeAfterBlockStmts : List Statement :=
  [ .block "blk" [.typeDecl tyT .empty, declNondet "x" (.tcons "T" []), declInit "y" tyB (var "x")]
      .empty,
    .typeDecl tyT .empty, declNondet "t" (.tcons "T" []), declInit "z" tyB (var "t") ]

/-- As `redeclaredTypeAfterBlockStmts`, with the block leaving its `b` unsolved. -/
private def redeclaredTypeAfterUnsolvedBlockStmts : List Statement :=
  [ .block "blk" [.typeDecl tyT .empty, declNondet "y" tyB] .empty,
    .typeDecl tyT .empty, declNondet "t" (.tcons "T" []), declInit "z" tyB (var "t") ]

/-- An outer `u : d`, a block solving its `b` to its `T`, then `v` at a `b` of its own, assigned
    to `u`. The outer `d` and the later `b` are solved to one another, not to `T`. -/
private def outerAssignedLaterTyVarStmts : List Statement :=
  [ declNondet "u" (.ftvar "d"),
    .block "blk" [.typeDecl tyT .empty, declNondet "x" (.tcons "T" []), declInit "y" tyB (var "x")]
      .empty,
    declNondet "v" tyB, Statement.set "u" (var "v") .empty ]

/-- An outer `w : c` assigned, inside a block, a variable at the block's `b`; after the block a
    `b` of its own is solved to `int`. -/
private def outerSolvedToBlockTyVarStmts : List Statement :=
  [ declNondet "w" (.ftvar "c"),
    .block "blk" [declNondet "y" tyB, Statement.set "w" (var "y") .empty] .empty,
    declInit "escaped" tyB (LExpr.intConst Core.coreLoc 1) ]

/-- As `outerSolvedToBlockTyVarStmts`, with `w` then assigned a Boolean. -/
private def outerSolvedToBlockTyVarFixedStmts : List Statement :=
  outerSolvedToBlockTyVarStmts ++ [Statement.set "w" (LExpr.boolConst Core.coreLoc true) .empty]

/-- A block solving its `b` to `int`, followed by a `b` of its own solved to `bool`. -/
private def blockIntThenOuterBoolStmts : List Statement :=
  [ .block "blk" [declInit "y" tyB (LExpr.intConst Core.coreLoc 1)] .empty,
    declInit "z" tyB (LExpr.boolConst Core.coreLoc true) ]

/-- An outer `b` solved to `int`, then a block whose declaration at `b` is initialized with a
    Boolean. The block sees the outer `b`, so the two conflict. -/
private def outerIntThenBlockBoolStmts : List Statement :=
  [ declInit "y" tyB (LExpr.intConst Core.coreLoc 1),
    .block "blk" [declInit "z" tyB (LExpr.boolConst Core.coreLoc true)] .empty ]

/-- Two branches of a conditional solving their own `b` to `int` and to `bool`. -/
private def branchesStmts : List Statement :=
  [ .ite .nondet [declInit "y" tyB (LExpr.intConst Core.coreLoc 1)]
      [declInit "z" tyB (LExpr.boolConst Core.coreLoc true)] .empty ]

/-- An outer `w : c` assigned, inside a block, a value of the block-local type `T`. The outer
    `c` is solved to `T`, which is not declared where `w` is. -/
private def outerTyVarToBlockTypeStmts : List Statement :=
  [ declNondet "w" (.ftvar "c"),
    .block "blk"
      [.typeDecl tyT .empty, declNondet "x" (.tcons "T" []), Statement.set "w" (var "x") .empty]
      .empty ]

/-- A Boolean `w`, a block solving its `b` to `int`, then an assertion annotating `w` with `b`,
    which is out of scope there. -/
private def annotationAfterBlockStmts : List Statement :=
  [ declInit "w" (.tcons "bool" []) (LExpr.boolConst Core.coreLoc true),
    .block "blk" [declInit "y" tyB (LExpr.intConst Core.coreLoc 1)] .empty,
    Statement.assert "a" (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "w" (some tyB))
                          (LExpr.boolConst Core.coreLoc true))
      .empty ]

/--
info: ok, declared types: [x : T, y : T], [x : U, y : U]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict siblingTypesStmts

/--
info: ok, declared types: [x : T, y : T], t : T, z : T
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict redeclaredTypeAfterBlockStmts

/--
info: ok, declared types: [y : b], t : T, z : T
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict redeclaredTypeAfterUnsolvedBlockStmts

/--
info: ok, declared types: u : b_1, [x : T, y : T], v : b_1
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerAssignedLaterTyVarStmts

/--
info: ok, declared types: w : b, [y : b], escaped : int
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerSolvedToBlockTyVarStmts

/--
info: ok, declared types: w : bool, [y : bool], escaped : int
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerSolvedToBlockTyVarFixedStmts

/--
info: ok, declared types: [y : int], z : bool
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict blockIntThenOuterBoolStmts

/--
info: Procedure 'P': Impossible to unify b with bool.
First mismatch: int with bool.
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerIntThenBlockBoolStmts

/--
info: ok, declared types: [y : int | z : bool]
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict branchesStmts

/--
info: Procedure 'P': Variable `w` has type `T`, which is not declared where `w` is declared. A
`type` declaration inside a body is in scope for the statements that follow it, and only within its
own block.
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict outerTyVarToBlockTypeStmts

/--
info: Procedure 'P': type variable `b` is not in scope
-/
#guard_msgs (whitespace := lax) in
#eval procVerdict annotationAfterBlockStmts

/-! ### The statement checker scopes written type variables itself -/

/--
info: ok, declared types: [x : T, y : T], escaped : int
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict tyVarSolvedInBlockThenUsedStmts

/--
info: Impossible to unify b with int.
First mismatch: T with int.
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict assignAfterBlockStmts

/--
info: ok, declared types: [x : T, y : T], z : b_1
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict outerTypeInnerSolveBody

/--
info: ok, declared types: [x : T, y : T], [x : U, y : U]
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict siblingTypesStmts

/--
info: ok, declared types: u : b_1, [x : T, y : T], v : b_1
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict outerAssignedLaterTyVarStmts

/--
info: ok, declared types: [y : int | z : bool]
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict branchesStmts

/--
info: Impossible to unify b with bool.
First mismatch: int with bool.
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict outerIntThenBlockBoolStmts

/--
info: type variable `b` is not in scope
-/
#guard_msgs (whitespace := lax) in
#eval stmtScopedVerdict annotationAfterBlockStmts

/-- A procedure whose block declares a type and a variable of that type. -/
private def typeDeclInBlockPgm : Program := { decls := [
  .proc { header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .block "b" [
              .typeDecl { name := "MyT", params := [] } .empty,
              Statement.init "x" (.forAll [] (.tcons "MyT" [])) .nondet .empty
            ] .empty
          ] } .empty
]}

/-- The type declared in the block of `typeDeclInBlockPgm` and the type of the variable after it,
    as the checker returns them. -/
private def blockTypeAndVar (p : Program) : Std.Format :=
  match p.decls with
  | [.proc proc _] =>
    match proc.body with
    | .structured [.block _ [.typeDecl d _, .cmd (.cmd (.init x ty _ _))] _] =>
      f!"type {d.name}; var {x} : {ty}"
    | _ => "unexpected shape"
  | _ => "unexpected shape"

/-- info: ACCEPTED: type MyT; var x : MyT -/
#guard_msgs in
#eval Core.TestUtil.verdictWith blockTypeAndVar
  ((Core.typeCheck .quiet typeDeclInBlockPgm none).mapError (·.message))

end BodyLocalTypeDeclScopeTests

section NondetCondTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (ExprOrNondet)

-- Type checking a nondet if: both branches should type-check
/--
info: ok: context:
types:   [(x, int)]
aliases: []
state:
tyGen: 0
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst:
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .ite .nondet
                      [Statement.set "x" eb[#1] .empty]
                      [Statement.set "x" eb[#2] .empty]
                      .empty,
                    .assert "x_pos" eb[(x == x)] .empty
                    ]
         return format ans.snd

end NondetCondTests

end Core

/-! ## Nondeterministic assignment target checking -/

namespace Strata.SetNondetTargetUncheckedTests

open Lambda Imperative

/-- A type environment with `x` bound at `ty`. -/
def envBinding (ty : LTy) : Core.Expression.TyEnv :=
  Core.CmdType.update Lambda.TEnv.default "x" ty

/-- The quantified scheme `∀ a. a`. -/
def polyTy : LTy := .forAll ["a"] (.ftvar "a")

/-- A scope binding `x` at a scheme that quantifies a type variable. -/
def polyEnv : Core.Expression.TyEnv := envBinding polyTy

/-- A scope binding `x` at a monotype. -/
def monoEnv : Core.Expression.TyEnv := envBinding (.forAll [] .int)

/-- The one-statement body `x := *`. -/
def body : List Core.Statement := [.cmd (.cmd (.set "x" .nondet #[]))]

/-- The statement checker's result on `x := *` in scope `Env`. -/
def run (Env : Core.Expression.TyEnv) :
    Except Strata.Message
      (List Core.Statement × Core.Expression.TyEnv × Core.Expression.TyContext) :=
  Core.Statement.typeCheckAux Core.initTyContext Env Core.Program.init none body

/-- The output statements and `x`'s binding from `run`, or the rejection. -/
def verdict (Env : Core.Expression.TyEnv) : Std.Format :=
  Core.TestUtil.verdictWith (fun (ss, EnvOut, _) =>
    f!"{ss}, x : {EnvOut.context.types.find? "x"}") (run Env)

/-! ## `x := *` is accepted only for a monotype `x`, which keeps its type -/

/--
info: REJECTED: Cannot set variable x of type ∀[a]. a. Polymorphic variable assignments are not allowed.
-/
#guard_msgs in
#eval verdict polyEnv

/--
info: ACCEPTED: {
  havoc x;
}, x : some int
-/
#guard_msgs in
#eval verdict monoEnv

/-! ## Missing targets are rejected -/

/-- info: REJECTED: Cannot set undeclared variable x. -/
#guard_msgs in
#eval verdict Lambda.TEnv.default

end Strata.SetNondetTargetUncheckedTests

/-! ## Assignment to a variable declared at an alias

The ambient scope declares `x : MyInt` and `z : b` under the alias `type MyInt := int`. -/

namespace Strata.SetAliasTests

open Lambda Imperative

def env : Core.Expression.TyEnv :=
  Lambda.TEnv.default.updateContext
    { types := Strata.Util.HMaps.ofScopes [[("x", .forAll [] (.tcons "MyInt" [])),
                                            ("z", .forAll [] (.ftvar "b"))]],
      aliases := [{ name := "MyInt", typeArgs := [], type := .tcons "int" [] }] }

/-- The starting context with `MyInt` also registered as a type. -/
def ctxReg : Core.Expression.TyContext :=
  { Core.initTyContext with knownTypes := Core.initTyContext.knownTypes.insert "MyInt" 0 }

/-- The checked statements with their own annotations and the final substitution, or the
    rejection. -/
def verdict (C : Core.Expression.TyContext) (ss : List Core.Statement) : Std.Format :=
  Core.TestUtil.verdictWith (fun (ss', E) =>
    f!"{ss'}, annotations {ss'.map Core.Statement.stmtOwnAnnotTys}, \
      substitution {E.stateSubstInfo.subst}")
    (Core.Statement.typeCheck C env Core.Program.init none ss)

/-! `x := 5` and `x := x` are accepted: `x` is assigned at the resolution `int` of `MyInt`. -/

/--
info: ACCEPTED: {
  x := 5;
}, annotations [[]], substitution []
-/
#guard_msgs in
#eval verdict Core.initTyContext [Core.Statement.set "x" (.intConst Core.coreLoc 5) .empty]

/--
info: ACCEPTED: {
  x := x;
}, annotations [[int]], substitution []
-/
#guard_msgs in
#eval verdict Core.initTyContext [Core.Statement.set "x" (.fvar Core.coreLoc "x" none) .empty]

/-! `x := z; var y : b := *` with `MyInt` also registered as a type: `b` is solved to `int`. -/

/--
info: ACCEPTED: {
  x := z;
  var y : int;
}, annotations [[int], [int]], substitution [[(b, int)]]
-/
#guard_msgs in
#eval verdict ctxReg
  [Core.Statement.set "x" (.fvar Core.coreLoc "z" none) .empty,
   Core.Statement.init "y" (.forAll [] (.ftvar "b")) .nondet .empty]

end Strata.SetAliasTests

/-! ## Initializer annotations

A checked declaration's annotation is its initializer's type, or closed if it has no initializer. -/

namespace Strata.InitResolvedTests

open Std (ToFormat Format format)
open Lambda Imperative
open Core.TestUtil (Env0 translate verdictOf)

mutual
/-- The declared type and initializer of every `init` in a statement, nested ones included. -/
def initsOfStmt : Core.Statement → List (LTy × Imperative.ExprOrNondet Core.Expression)
  | .cmd (.cmd (.init _ ty e _)) => [(ty, e)]
  | .cmd _ => []
  | .block _ bss _ => initsOfStmts bss
  | .ite _ tss ess _ => initsOfStmts tss ++ initsOfStmts ess
  | .loop _ _ _ bss _ => initsOfStmts bss
  | _ => []

/-- List form of `initsOfStmt`. -/
def initsOfStmts : List Core.Statement → List (LTy × Imperative.ExprOrNondet Core.Expression)
  | [] => []
  | s :: rest => initsOfStmt s ++ initsOfStmts rest
end

/-- The type `LExpr.typeCheck` assigns `e` in the empty de Bruijn context. -/
def checkedTy (e : Core.Expression.Expr) : Format :=
  match LExpr.typeCheck (T := Core.CoreLParams) [] e with
  | some t => format t
  | none => f!"ILL-TYPED"

/-- Whether an `init` agrees with its monomorphic annotation: a deterministic initializer has
    that type, and a nondeterministic one's annotation is closed. -/
def initResolvedB : LTy × Imperative.ExprOrNondet Core.Expression → Bool
  | (.forAll [] mty, .det e) => LExpr.typeCheck (T := Core.CoreLParams) [] e == some mty
  | (.forAll [] mty, .nondet) => mty.freeVars == []
  | _ => false

/-- The stored annotation of one `init`, the type of its initializer, and whether the two
    agree. -/
def describeInit : LTy × Imperative.ExprOrNondet Core.Expression → Format
  | (.forAll [] mty, .det e) =>
    f!"det annot {mty} init {checkedTy e} resolved {initResolvedB (.forAll [] mty, .det e)}"
  | (.forAll [] mty, .nondet) =>
    f!"nondet annot {mty} freeVars {mty.freeVars}"
  | (ty, _) => f!"annotation NOT quantifier-free {ty}"

/-- Every `init` of a statement list, described. -/
def describe (ss : List Core.Statement) : Format :=
  Format.joinSep ((initsOfStmts ss).map describeInit) (" / " : Format)

/-- The statements of the first procedure among some declarations. -/
def bodyOf (ds : List Core.Decl) : List Core.Statement :=
  match ds.find? (fun d => match d with | .proc _ _ => true | _ => false) with
  | some (.proc d _) =>
    match d.body with
    | .structured ss => ss
    | .cfg _ => []
  | _ => []

/-- The starting context extended with every declared function. -/
def ctxOfAll (ds : List Core.Decl) : Core.Expression.TyContext :=
  ds.foldl (fun C d =>
    match d with
    | .func f _ => C.addFactoryFunction f.toLFunc
    | _ => C) Core.initTyContext

/-- Runs the statement checker on the first procedure body. -/
def runAux (p : StrataDDM.Program) :
    Except Strata.Message
      (List Core.Statement × Core.Expression.TyEnv × Core.Expression.TyContext) :=
  let ds := (translate p).decls
  Core.Statement.typeCheckAux (ctxOfAll ds) Env0 Core.Program.init none (bodyOf ds)

/-- Describes every `init` in the checked procedure body. -/
def reportAux (p : StrataDDM.Program) : Format :=
  match runAux p with
  | .error e => f!"typeCheckAux failed: {e.format none}"
  | .ok (ssA, _, _) => describe ssA

/-- The verdict on the first procedure body, with the message of any rejection. -/
def auxVerdict (p : StrataDDM.Program) : Format :=
  verdictOf ((runAux p).mapError (·.message))

/-! ## Initializer cases -/

/-- An initializer calling a generic function whose result type parameter no argument
    determines. -/
private def pickPgm : StrataDDM.Program :=
#strata
program Core;

function pick<a, b>(x : a) : Map a b;

procedure test()
{
  var m : Map int bool := pick(1);
};
#end

/-- An initializer calling a generic function whose result type is a bare type parameter. -/
private def nothingPgm : StrataDDM.Program :=
#strata
program Core;

function nothing<a>() : a;

procedure test()
{
  var x : int := nothing();
};
#end

/-- Initializers whose types do not depend on the declared type. -/
private def determinedPgm : StrataDDM.Program :=
#strata
program Core;

procedure test()
{
  var i : int := 1;
  var b : bool := true;
  var s : Sequence int := Sequence.empty<int>();
  var t : Map int bool := mapConst<int>(true);
};
#end

private def nondetPgm : StrataDDM.Program :=
#strata
program Core;

procedure test()
{
  var y : int;
};
#end

/-- Declarations inside both branches of a conditional and inside a loop body. -/
private def nestedPgm : StrataDDM.Program :=
#strata
program Core;

function nothing<a>() : a;

procedure test()
{
  if (true) {
    var x : int := nothing();
  } else {
    var y : bool := nothing();
  }
  while (false) {
    var z : string := nothing();
  }
};
#end

/-- Two declarations calling one generic function at different types. -/
private def twoPgm : StrataDDM.Program :=
#strata
program Core;

function nothing<a>() : a;

procedure test()
{
  var x : int := nothing();
  var y : bool := nothing();
};
#end

/-- A declared type the initializer's type cannot meet. -/
private def illTypedPgm : StrataDDM.Program :=
#strata
program Core;

procedure test()
{
  var i : bool := 1;
};
#end

/-! ## Annotation and initializer agreement -/

/--
info: det annot (Map int bool) init (Map int bool) resolved true
-/
#guard_msgs (whitespace := lax) in
#eval reportAux pickPgm

/--
info: det annot int init int resolved true
-/
#guard_msgs (whitespace := lax) in
#eval reportAux nothingPgm

/-! Agreement inside conditional branches and a loop body. -/
/--
info: det annot int init int resolved true / det annot bool init bool resolved true /
  det annot string init string resolved true
-/
#guard_msgs (whitespace := lax) in
#eval reportAux nestedPgm

/-! Each declaration's annotation agrees independently. -/
/--
info: det annot int init int resolved true / det annot bool init bool resolved true
-/
#guard_msgs (whitespace := lax) in
#eval reportAux twoPgm

/-! Initializers not refined by the declared type agree. -/
/--
info: det annot int init int resolved true / det annot bool init bool resolved true /
  det annot (Sequence int) init (Sequence int) resolved true /
  det annot (Map int bool) init (Map int bool) resolved true
-/
#guard_msgs (whitespace := lax) in
#eval reportAux determinedPgm

/-! A nondeterministic declaration at a concrete type keeps a closed annotation. -/
/--
info: nondet annot int freeVars []
-/
#guard_msgs (whitespace := lax) in
#eval reportAux nondetPgm

/-! ## Accepted and rejected programs -/

/--
info: [ACCEPTED, ACCEPTED, ACCEPTED, ACCEPTED, ACCEPTED, ACCEPTED]
-/
#guard_msgs (whitespace := lax) in
#eval f!"{[pickPgm, nothingPgm, determinedPgm, nondetPgm, nestedPgm, twoPgm].map auxVerdict}"

/-! A declared type that cannot unify with the initializer's type is rejected. -/
/--
info: REJECTED: Impossible to unify bool with int.
-/
#guard_msgs (whitespace := lax) in
#eval auxVerdict illTypedPgm

end Strata.InitResolvedTests

namespace Core

section CallOutArgTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (ExprOrNondet)

/-- A test procedure: `procedure Foo(inout x: int, out y: int)` -/
private def testProc : Procedure :=
  { header := {
      name := ⟨"Foo", ()⟩,
      typeArgs := [],
      inputs := [(⟨"x", ()⟩, .int)],
      outputs := [(⟨"x", ()⟩, .int), (⟨"y", ()⟩, .int)] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

private def testProgram : Program :=
  { decls := [.proc testProc .empty] }

-- The inout parameter `x` takes an `inout` argument, so an input value for it with
-- its result as a separate `out x` is refused.
/--
info: error: [call Foo(x == x, out x, out y);]: Ill-formed call: the call to Foo passes an input value for x, which is an inout parameter and must be passed as inout
-/
#guard_msgs in
#eval do
  let env := TEnv.default.updateContext
    { types := Strata.Util.HMaps.ofScopes [[("x", t[int]), ("y", t[int])]] }
  let ans ← Statement.typeCheck LContext.default env testProgram none
    [.cmd (.call "Foo" [.inArg eb[x == x], .outArg ⟨"x", ()⟩, .outArg ⟨"y", ()⟩] .empty)]
  return format ans

-- The same holds when the input value is the variable `x` itself.
/--
info: error: [call Foo(x, out x, out y);]: Ill-formed call: the call to Foo passes an input value for x, which is an inout parameter and must be passed as inout
-/
#guard_msgs in
#eval do
  let env := TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[int]), ("y", t[int])]] }
  let ans ← Statement.typeCheck LContext.default env testProgram none
    [.cmd (.call "Foo" [.inArg eb[x], .outArg ⟨"x", ()⟩, .outArg ⟨"y", ()⟩] .empty)]
  return format ans

-- Passing `x` as an `inout` argument succeeds.
/-- info: ok: () -/
#guard_msgs in
#eval do
  let env := TEnv.default.updateContext
    { types := Strata.Util.HMaps.ofScopes [[("x", t[int]), ("y", t[int])]] }
  let _ ← Statement.typeCheck LContext.default env testProgram none
    [.cmd (.call "Foo" [.inoutArg ⟨"x", ()⟩, .outArg ⟨"y", ()⟩] .empty)]
  return format ()

end CallOutArgTests

section ReservedTyVarNameTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Core.TestUtil (declNondet)

/-! A declared type, free-variable annotation or binder annotation may not name a type variable
in the reserved `$__ty*` or `$__rigid_*` namespaces, whatever the generator state. -/

/-- Checks `ss` with `y : int` in scope. -/
private def reservedVerdict (ss : List Statement) : Format :=
  Core.TestUtil.verdictOf (Statement.typeCheck LContext.default
      (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("y", t[int])]] })
      Program.init none ss)

/-- An assertion whose unannotated binder makes the checker generate a type variable. -/
private def generatingAssert : Statement :=
  .assert "g" (LExpr.all Core.coreLoc "z" none (LExpr.boolConst Core.coreLoc true)) .empty

/-- An assertion that `y`, annotated with `ty`, equals `0`. -/
private def annotatedAssert (ty : LMonoTy) : Statement :=
  .assert "a" (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "y" (some ty))
               (LExpr.intConst Core.coreLoc 0)) .empty

/--
info: REJECTED: Type $__ty0 contains a free type variable that is not admissible here.
-/
#guard_msgs in
#eval reservedVerdict [declNondet "x" (.ftvar "$__ty0")]

/--
info: REJECTED: Type $__ty0 contains a free type variable that is not admissible here.
-/
#guard_msgs in
#eval reservedVerdict [generatingAssert, generatingAssert, declNondet "x" (.ftvar "$__ty0")]

/--
info: REJECTED: Type (Map $__ty0 int) contains a free type variable that is not admissible here.
-/
#guard_msgs in
#eval reservedVerdict [generatingAssert, generatingAssert,
  declNondet "x" (.tcons "Map" [.ftvar "$__ty0", .int])]

/--
info: REJECTED: Type $__rigid_a contains a free type variable that is not admissible here.
-/
#guard_msgs in
#eval reservedVerdict [declNondet "x" (.ftvar "$__rigid_a")]

/-- info: ACCEPTED -/
#guard_msgs in
#eval reservedVerdict [declNondet "x" (.ftvar "b")]

/-- info: ACCEPTED -/
#guard_msgs in
#eval reservedVerdict [declNondet "x" .int]

/--
info: REJECTED: type variable `$__ty999` is not in scope
-/
#guard_msgs in
#eval reservedVerdict [annotatedAssert (.ftvar "$__ty999")]

/--
info: REJECTED: type variable `$__ty0` is not in scope
-/
#guard_msgs in
#eval reservedVerdict [annotatedAssert (.ftvar "$__ty0")]

/--
info: REJECTED: type variable `$__ty0` is not in scope
-/
#guard_msgs in
#eval reservedVerdict [generatingAssert, generatingAssert, annotatedAssert (.ftvar "$__ty0")]

/--
info: REJECTED: type variable `$__rigid_a` is not in scope
-/
#guard_msgs in
#eval reservedVerdict [annotatedAssert (.ftvar "$__rigid_a")]

-- A type variable a user may write is rejected when no declaration in scope wrote it.
/-- info: REJECTED: type variable `c` is not in scope -/
#guard_msgs in
#eval reservedVerdict [annotatedAssert (.ftvar "c")]

/-- info: ACCEPTED -/
#guard_msgs in
#eval reservedVerdict [annotatedAssert .int]

-- Linking the annotation `int` to an inferred type `$__ty5` is rejected while the type-variable
-- generator is at 0: `$__ty5` has not been generated yet.
/--
info: REJECTED: Resolved annotated type contains a future generated type variable
-/
#guard_msgs in
#eval Core.TestUtil.verdictOf
  (Core.SourceExpr.linkAnnot LContext.default false .int (.ftvar "$__ty5") TEnv.default)

/--
info: REJECTED: type variable `$__ty999` is not in scope
-/
#guard_msgs in
#eval reservedVerdict
  [.assert "b" (LExpr.all Core.coreLoc "x" (some (.ftvar "$__ty999"))
                (LExpr.boolConst Core.coreLoc true)) .empty]

/--
info: REJECTED: type variable `$__rigid_a` is not in scope
-/
#guard_msgs in
#eval reservedVerdict
  [.init "f" (.forAll [] (.ftvar "b"))
    (.det (.abs Core.coreLoc "z" (some (.ftvar "$__rigid_a")) (.bvar Core.coreLoc 0))) .empty]

end ReservedTyVarNameTests

section BinderAnnotationTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Core.TestUtil (declNondet)

/-! A binder annotation binds no type variable: each of its type variables must be rigid or written
by an earlier declaration in scope, and the annotation then denotes that type. -/

/-- Checks the statements under `C` and `Env` and shows the stored statements, or the error. -/
private def storedStmts (ss : List Statement) (C : LContext CoreLParams := LContext.default)
    (Env : TEnv Unit := TEnv.default) : Format :=
  match Statement.typeCheck C Env Program.init none ss with
  | .ok (ss', _) => format ss'
  | .error e => f!"REJECTED: {e}"

/-- An assumption `forall x : ty :: x == x`. -/
private def reflAssume (ty : LMonoTy) : Statement :=
  .assume "h" (LExpr.all Core.coreLoc "x" (some ty)
               (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))) .empty

/-- A declaration `var f : b := e`. -/
private def declB (e : Expression.Expr) : Statement :=
  .init "f" (.forAll [] (.ftvar "b")) (.det e) .empty

-- No declaration wrote `b`.
/--
info: REJECTED: type variable `b` is not in scope
-/
#guard_msgs in
#eval storedStmts [reflAssume (.ftvar "b")]

-- The declaration binds its own `b`; the binder's `c` is not in scope.
/--
info: REJECTED: type variable `c` is not in scope
-/
#guard_msgs in
#eval storedStmts [declB (.abs Core.coreLoc "z" (some (.ftvar "c")) (.bvar Core.coreLoc 0))]

-- The lambda body would solve `c` to `int`, but `c` is not in scope.
/--
info: REJECTED: type variable `c` is not in scope
-/
#guard_msgs in
#eval storedStmts
  [declB (.abs Core.coreLoc "z" (some (.ftvar "c"))
          (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.intConst Core.coreLoc 1)))]

-- Neither `b` nor `c` is in scope; the first one met is reported.
/--
info: REJECTED: type variable `b` is not in scope
-/
#guard_msgs in
#eval storedStmts
  [.assume "h" (LExpr.all Core.coreLoc "x" (some (.ftvar "b"))
    (LExpr.all Core.coreLoc "y" (some (.ftvar "c"))
      (.eq Core.coreLoc (.bvar Core.coreLoc 1) (.bvar Core.coreLoc 0)))) .empty]

-- A rigid type variable is in scope, and the binder denotes it.
/--
info: {
  assume [h]: forall x : (b) :: x == x;
}
-/
#guard_msgs in
#eval storedStmts [reflAssume (.ftvar "b")] { LContext.default with rigidTypeVars := ["b"] }

-- A binder annotation may not name a type variable in the generator namespace.
/--
info: REJECTED: type variable `$__ty999` is not in scope
-/
#guard_msgs in
#eval storedStmts [reflAssume (.ftvar "$__ty999")]

/-! When a check solves an in-scope type variable to a generated one, the output names the
in-scope variable. -/

-- Comparing `y` with the binder solves `y`'s `b` to a generated variable; both store `b`.
/--
info: {
  var y : (b);
  assert [a]: forall q : (b) :: y == q;
}
-/
#guard_msgs in
#eval storedStmts
  [declNondet "y" (.ftvar "b"),
   .assert "a" (LExpr.all Core.coreLoc "q" (some (.ftvar "b"))
                (.eq Core.coreLoc (.fvar Core.coreLoc "y" none) (.bvar Core.coreLoc 0)))
    .empty]

-- The binder has no annotation; its generated type is unified with `y`'s `b`.
/--
info: {
  var y : (b);
  assert [a]: forall q : (b) :: y == q;
}
-/
#guard_msgs in
#eval storedStmts
  [declNondet "y" (.ftvar "b"),
   .assert "a" (LExpr.all Core.coreLoc "q" none
                (.eq Core.coreLoc (.fvar Core.coreLoc "y" none) (.bvar Core.coreLoc 0))) .empty]

-- `f`'s type is solved through a lambda over `b` and a comparison with an unannotated lambda.
/--
info: {
  var y : (b);
  var f : b -> b := fun z : (b) => z;
  assert [a]: f == (fun z : (b) => z);
}
-/
#guard_msgs in
#eval storedStmts
  [declNondet "y" (.ftvar "b"),
   .init "f" (.forAll [] (.ftvar "c"))
       (.det (.abs Core.coreLoc "z" (some (.ftvar "b")) (.bvar Core.coreLoc 0))) .empty,
   .assert "a" (.eq Core.coreLoc (.fvar Core.coreLoc "f" none)
                (.abs Core.coreLoc "z" none (.bvar Core.coreLoc 0))) .empty]

-- The later `b` is not the block's, so `y2` and the binder store it as `b_1`.
/--
info: {
  blk :
  {
    var y : (b);
  }
  var y2 : (b_1);
  assert [a]: forall q : (b_1) :: y2 == q;
}
-/
#guard_msgs in
#eval storedStmts
  [.block "blk" [declNondet "y" (.ftvar "b")] .empty,
   declNondet "y2" (.ftvar "b"),
   .assert "a" (LExpr.all Core.coreLoc "q" (some (.ftvar "b"))
                (.eq Core.coreLoc (.fvar Core.coreLoc "y2" none) (.bvar Core.coreLoc 0)))
    .empty]

end BinderAnnotationTests

/-! ## Type variables of expression annotations must be in scope

Each must be a rigid type parameter or written by an earlier declaration in an open scope. -/

namespace AnnotationScopeTests

open Lambda Imperative
open Core.TestUtil (Env0 declNondet printEach stmtEnv tv var verdictOf)

private def assertE (e : Expression.Expr) : Statement := Statement.assert "a" e .empty

private def annot (x : String) (ty : LMonoTy) : Expression.Expr := LExpr.fvar Core.coreLoc x
    (some ty)

/-- `storedStmts` in the initial typing context and a statement environment. -/
private def verdict (ss : List Statement) : Std.Format :=
  storedStmts ss initTyContext stmtEnv

-- `var x : int; assert ((x : %a) == 0)`: no declaration wrote `a`.
/-- info: REJECTED: type variable `a` is not in scope -/
#guard_msgs in
#eval verdict [declNondet "x" .int, assertE
               (.eq Core.coreLoc (annot "x" (tv "a")) (.intConst Core.coreLoc 0))]

-- `var y : %b := 1; assert ((y : %b) == 1)`: the annotation denotes the type `b` stands for.
/--
info: {
  var y : int := 1;
  assert [a]: y == 1;
}
-/
#guard_msgs in
#eval verdict [declInit "y" (tv "b") (.intConst Core.coreLoc 1),
  assertE (.eq Core.coreLoc (annot "y" (tv "b")) (.intConst Core.coreLoc 1))]

-- `{var y : %b := 1}; var w : bool; assert ((w : %b) == true)`: the block's `b` is out of scope.
/-- info: REJECTED: type variable `b` is not in scope -/
#guard_msgs in
#eval verdict [.block "blk" [declInit "y" (tv "b") (.intConst Core.coreLoc 1)] .empty, declNondet
               "w" .bool,
  assertE (.eq Core.coreLoc (annot "w" (tv "b")) (.boolConst Core.coreLoc true))]

-- `var y : %b := 1; assert (forall q : %b :: q == y)`: the binder denotes `int`.
/--
info: {
  var y : int := 1;
  assert [a]: forall q : int :: q == y;
}
-/
#guard_msgs in
#eval verdict [declInit "y" (tv "b") (.intConst Core.coreLoc 1),
  assertE (LExpr.all Core.coreLoc "q" (some (tv "b"))
           (.eq Core.coreLoc (.bvar Core.coreLoc 0) (var "y")))]

-- `var y : %b := 1; assert (forall q : %b :: q == true)`: the binder's type is `int`, not `bool`.
/--
info: REJECTED: Impossible to unify bool with b.
First mismatch: int with bool.
-/
#guard_msgs in
#eval verdict [declInit "y" (tv "b") (.intConst Core.coreLoc 1),
  assertE (LExpr.all Core.coreLoc "q" (some (tv "b"))
           (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.boolConst Core.coreLoc true)))]

/-- Checks a one-procedure program and shows it, or the error. -/
private def procShown (typeArgs : List TyIdentifier) (inputs : @LMonoTySignature Unit)
    (body : List Statement) : Std.Format :=
  match Core.Program.typeCheck initTyContext Env0 (bodyPgm body typeArgs inputs) with
  | .ok (p', _) => Std.format p'
  | .error e => f!"REJECTED: {e.message}"

-- `procedure P<a>(x : a) { assert ((x : a) == x) }`: a type parameter is rigid, so it is in scope.
/--
info: program Core;

procedure P<a> (x : a)
{
  assert [a]: x == x;
};
-/
#guard_msgs in
#eval procShown ["a"] [("x", tv "a")] [assertE (.eq Core.coreLoc (annot "x" (tv "a")) (var "x"))]

open Strata.Util (HMaps)

/-! ## Annotations at a type variable solved earlier or declared later -/

/-- Solves `a` to the type of `value`, then declares `x : int`. -/
private def solvedPrefix (value : Core.Expression.Expr) : List Statement :=
  [ declNondet "seed" (.ftvar "a"),
    Statement.assert "solveA"
      (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "seed" none) value) .empty,
    declNondet "x" .int ]

/-- An assertion annotating `x` with `a`. -/
private def annotatedXAssertion : Statement :=
  Statement.assert "xAtA"
    (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "x" (some (.ftvar "a")))
      (LExpr.intConst Core.coreLoc 0)) .empty

/-- The solution of `a` after checking `ss`, or the rejection. -/
private def solutionOfA (ss : List Statement) : Std.Format :=
  match Statement.typeCheckAux initTyContext stmtEnv Program.init none ss with
  | .error e => f!"REJECTED: {e}"
  | .ok (_, Env, _) => f!"a := {HMaps.find? Env.stateSubstInfo.subst "a"}"

private def annotatedXAfter (ss : List Statement) : Std.Format :=
  verdictOf (Statement.typeCheckAux initTyContext stmtEnv Program.init none
    (ss ++ [annotatedXAssertion]))

private def boolSolvedPrefix : List Statement :=
  solvedPrefix (LExpr.boolConst Core.coreLoc true)

private def intSolvedPrefix : List Statement :=
  solvedPrefix (LExpr.intConst Core.coreLoc 1)

/--
info: a := some bool
REJECTED: Impossible to unify a with int.
First mismatch: bool with int.
-/
#guard_msgs in
#eval printEach [solutionOfA boolSolvedPrefix, annotatedXAfter boolSolvedPrefix]

/--
info: a := some int
ACCEPTED
-/
#guard_msgs in
#eval printEach [solutionOfA intSolvedPrefix, annotatedXAfter intSolvedPrefix]

/-- Declares `x : int`, with `a` unconstrained. -/
private def unsolvedAnnotationPrefix : List Statement :=
  [ declNondet "x" .int ]

/-- `x : a` before any declaration at `a`, then a declaration at `a` solved to the type of
    `value`. -/
private def solveAnnotationAfterOccurrence (value : Core.Expression.Expr) : List Statement :=
  unsolvedAnnotationPrefix ++
    [ annotatedXAssertion,
      declNondet "later" (.ftvar "a"),
      Statement.assert "solveLater"
        (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "later" none) value) .empty ]

private def annotationSolvedLater (value : Core.Expression.Expr) : Std.Format :=
  verdictOf (Statement.typeCheckAux initTyContext stmtEnv Program.init none
    (solveAnnotationAfterOccurrence value))

-- `a` is unsolved after `x : int`; annotating with `a` before its declaration is rejected.
/--
info: a := none
REJECTED: type variable `a` is not in scope
REJECTED: type variable `a` is not in scope
-/
#guard_msgs in
#eval printEach [solutionOfA unsolvedAnnotationPrefix,
  annotationSolvedLater (LExpr.boolConst Core.coreLoc true),
  annotationSolvedLater (LExpr.intConst Core.coreLoc 1)]

/-! ## Operator annotations are schematic; binder annotations read the scope -/

/-- A polymorphic identity function. -/
private def annotationIdentity : LFunc CoreLParams :=
  LFunc.mk (⟨"annotationIdentity", ()⟩ : CoreIdent)
    (typeArgs := ["t"])
    (inputs := [(⟨"value", ()⟩, .ftvar "t")])
    (output := .ftvar "t")

private def annotationIdentityContext : Expression.TyContext :=
  initTyContext.addFactoryFunction annotationIdentity

/-- `annotationIdentity` annotated with `a → a`, applied to an integer. -/
private def operatorAnnotationExpression : Expression.Expr :=
  LExpr.eq Core.coreLoc
    (LExpr.app Core.coreLoc
      (LExpr.op Core.coreLoc (⟨"annotationIdentity", ()⟩ : CoreIdent)
        (some (.arrow (.ftvar "a") (.ftvar "a"))))
      (LExpr.intConst Core.coreLoc 0))
    (LExpr.intConst Core.coreLoc 0)

/-- A lambda whose binder is annotated with `a`, applied to an integer. -/
private def binderAnnotationExpression : Expression.Expr :=
  LExpr.eq Core.coreLoc
    (LExpr.app Core.coreLoc
      (LExpr.abs Core.coreLoc "value" (some (.ftvar "a")) (LExpr.bvar Core.coreLoc 0))
      (LExpr.intConst Core.coreLoc 0))
    (LExpr.intConst Core.coreLoc 0)

/-- The verdict on `e` when a later statement solves `a` to the type of `value`. -/
private def expressionBeforeLaterSolution
    (C : Expression.TyContext) (e value : Expression.Expr) : Std.Format :=
  verdictOf (Statement.typeCheckAux C stmtEnv Program.init none
    [ Statement.assert "source" e .empty,
      declNondet "later" (.ftvar "a"),
      Statement.assert "solveLater"
          (LExpr.eq Core.coreLoc (LExpr.fvar Core.coreLoc "later" none) value) .empty ])

/-- The verdict on `e`, checked after `boolSolvedPrefix` solved `a` to `bool`. -/
private def expressionAfterExistingSolution
    (C : Expression.TyContext) (e : Expression.Expr) : Std.Format :=
  verdictOf do
    let (_, Env, _) ← Statement.typeCheckAux C stmtEnv Program.init none boolSolvedPrefix
    Statement.typeCheckAux C Env Program.init none [Statement.assert "source" e .empty]

/--
info: ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printEach [
  expressionBeforeLaterSolution annotationIdentityContext operatorAnnotationExpression
    (LExpr.boolConst Core.coreLoc true),
  expressionAfterExistingSolution annotationIdentityContext operatorAnnotationExpression]

-- A binder's `a` is not in scope when declared only later or in a separate check.
/--
info: REJECTED: type variable `a` is not in scope
REJECTED: type variable `a` is not in scope
-/
#guard_msgs in
#eval printEach [
  expressionBeforeLaterSolution initTyContext binderAnnotationExpression
      (LExpr.boolConst Core.coreLoc true),
  expressionAfterExistingSolution initTyContext binderAnnotationExpression]

end AnnotationScopeTests

end Core

end
