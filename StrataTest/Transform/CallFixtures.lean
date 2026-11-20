/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core
public meta import Strata.Transform.CoreTransform
public meta import Strata.Transform.ProcedureInlining
public meta import StrataTest.Languages.Core.Tests.TestUtil

/-! # Fully annotated calls of polymorphic procedures

Each program pairs a procedure `Caller` with a callee declaration given as an
argument. Every expression of `Caller` carries its type annotations, except the
argument `unknownArg`. The file also holds the runner that inlines every call
and the fixtures whose callee captures a type. -/

meta section

public section

namespace Core.CallFixtures

open Lambda Core.TestUtil Core.Transform ProcedureInlining

/-- The variable `x` annotated with type `ty`. -/
def v (x : String) (ty : LMonoTy) : Expression.Expr := .fvar Core.coreLoc x (some ty)

/-- The integer literal `7`. -/
def int7 : Expression.Expr := .intConst Core.coreLoc 7

/-- The equality `a == b`. -/
def eqE (a b : Expression.Expr) : Expression.Expr := .eq Core.coreLoc a b

/-- `forall y : ty :: y == y`. -/
def reflAll (ty : LMonoTy) : Expression.Expr :=
  .all Core.coreLoc "y" (some ty) (eqE (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))

/-- The procedure `Caller<typeArgs>(ins)` with body `body` and no spec. -/
def caller (typeArgs : List String) (ins : @LMonoTySignature Unit)
    (body : List Statement) : Decl :=
  mkProc "Caller" typeArgs ins [] body

/-- An argument whose type is unknown: an application of an unannotated
    operator. -/
def unknownArg : Expression.Expr := .app Core.coreLoc (.op Core.coreLoc "Int.Neg" none) int7

/-- `idp<a>(x : a, out r : a)` called with `7`; `ai : int`. -/
def idpProg (idp : Decl) : Program := { decls := [idp,
  caller [] [] [declNondet "ai" .int, callS "idp" [.inArg int7, .outArg "ai"]]] }

/-- `swap<a>(inout x : a, inout y : a)` called on two `int` variables. -/
def swapProg (swap : Decl) : Program := { decls := [swap,
  caller [] [] [declNondet "i" .int, declNondet "j" .int,
    callS "swap" [.inoutArg "i", .inoutArg "j"]]] }

/-- `p<a>(s : Sequence (Sequence a))` called with a
    `Sequence (Sequence int)`. -/
def seqProg (p : Decl) : Program := { decls := [p,
  caller [] [("t", seqTy (seqTy .int))]
    [callS "p" [.inArg (v "t" (seqTy (seqTy .int)))]]] }

/-- A caller with type parameter `a` calls `idp`, whose parameter is also
    `a`. -/
def sameNameProg (idp : Decl) : Program := { decls := [idp,
  caller ["a"] [("z", tv "a")]
    [declNondet "w" (tv "a"), callS "idp" [.inArg (v "z" (tv "a")), .outArg "w"]]] }

/-- `pair<a, b>(x : a, y : b, out r : a)` called as `pair(y, x, out w)` with
    `x : a`, `y : b`. -/
def pairProg (pair : Decl) : Program := { decls := [pair,
  caller ["a", "b"] [("x", tv "a"), ("y", tv "b")]
    [declNondet "w" (tv "b"),
     callS "pair" [.inArg (v "y" (tv "b")), .inArg (v "x" (tv "a")), .outArg "w"]]] }

/-- `q<a>()` requiring `forall y : a :: y == y`. -/
def qReflDecl : Decl := mkProc "q" ["a"] [] [] (pre := [reflAll (tv "a")])

/-- `q<a>()` called with no arguments, so the call does not determine `a`. -/
def qProg (q : Decl) : Program := { decls := [q, caller [] [] [callS "q" []]] }

/-- `r<a, b>(x : a)` called with `7`, which does not determine `b`. -/
def rProg (r : Decl) : Program :=
  { decls := [r, caller [] [] [callS "r" [.inArg int7]]] }

/-- `q<a>(x : a)` requiring `forall y : a :: y == y`. -/
def qArgDecl : Decl :=
  mkProc "q" ["a"] [("x", tv "a")] [] (pre := [reflAll (tv "a")])

/-- `P<b>(y : b)` calls `q` with its own parameter `y`, so the call determines
    `a` as the caller's type parameter `b`. -/
def qParamProg (q : Decl) : Program := { decls := [q,
  mkProc "P" ["b"] [("y", tv "b")] [] [callS "q" [.inArg (v "y" (tv "b"))]]] }

/-- `q<a>()` called with the stored type arguments `tyArgs`. -/
def qTyArgsProg (q : Decl) (tyArgs : Option (List LTy)) : Program :=
  { decls := [q, caller [] [] [.cmd (.call "q" tyArgs [] .empty)]] }

/-- `r<a, b>(x : a)` called with `7` and the stored type arguments `tyArgs`. -/
def rTyArgsProg (r : Decl) (tyArgs : Option (List LTy)) : Program :=
  { decls := [r, caller [] [] [.cmd (.call "r" tyArgs [.inArg int7] .empty)]] }

/-- `callee<a>(x : a)` called with the stored type arguments `tyArgs`. The argument `s` has the
    type `Sequence $__ty0`, with `$__ty0` a generated type variable. -/
def genArgProg (callee : Decl) (name : String) (tyArgs : Option (List LTy)) : Program :=
  { decls := [callee, caller [] [] [declNondet "s" (seqTy (tv "$__ty0")),
    .cmd (.call name tyArgs [.inArg (v "s" (seqTy (tv "$__ty0")))] .empty)]] }

/-- `callee<a, b>(x : a, y : b)` called with the stored type arguments `tyArgs`. Both arguments
    have the type `$__ty0`, a generated type variable, so the call gives `a` and `b` one type. -/
def genPairArgProg (callee : Decl) (name : String) (tyArgs : Option (List LTy)) : Program :=
  { decls := [callee, caller [] [] [declNondet "s" (tv "$__ty0"),
    .cmd (.call name tyArgs [.inArg (v "s" (tv "$__ty0")), .inArg (v "s" (tv "$__ty0"))]
      .empty)]] }

/-- `r<a, b>(x : a)` called with an argument of unknown type. -/
def unknownProg (r : Decl) : Program :=
  { decls := [r, caller [] [] [callS "r" [.inArg unknownArg]]] }

/-- `idp` called with `7` into `bb : bool`, so `a` would need two types. -/
def conflictProg (idp : Decl) : Program := { decls := [idp,
  caller [] [] [declNondet "bb" .bool, callS "idp" [.inArg int7, .outArg "bb"]]] }

/-- `p` with every call inlined, or the error that inlining raises. The type names the inlining
    generates avoid the names already in `p`. -/
def tryInlineCall (p : Program) : Except Strata.Message Program :=
  let taken := p.typeNamesWithPrefix ProcedureInlining.inlineTyPrefix
  match (declareGeneratedTypes ProcedureInlining.inlineTyPrefix taken
      (runProgramTyped (targetProcList := .none) (inlineCallCmd taken) p) .emp) with
  | ⟨.ok (_, res), _⟩ => .ok res
  | ⟨.error e, _⟩ => .error e

/-- `p` with every call inlined. -/
def runInlineCall (p : Program) : Program :=
  match tryInlineCall p with
  | .ok res => res
  | .error e => panic! (toString e) -- nopanic:ok

/-- `forall x : ty, y : ty :: x == y`: true exactly when `ty` has one value. -/
def singletonAll (ty : LMonoTy) : Expression.Expr :=
  .all Core.coreLoc "x" (some ty)
      (.all Core.coreLoc "y" (some ty) (eqE (.bvar Core.coreLoc 1) (.bvar Core.coreLoc 0)))

/-- A program declaring the type `tyName`, an axiom making it a singleton, a
    callee `Q<a>()` with preconditions `pre` and body `body`, and `P` calling `Q`.
    `tyName` is the name a transform generates for the type argument that the
    call does not determine. -/
def capturedTypeProg (tyName : String) (pre : List Expression.Expr)
    (body : List Statement) : Program := { decls := [
  .type (.con { name := tyName, params := [] }) .empty,
  .ax { name := "one", e := singletonAll (.tcons tyName []) } .empty,
  mkProc "Q" ["a"] [] [] body pre,
  mkProc "P" [] [] [] [callS "Q" []]] }

/-- A callee `Q<a>()` with preconditions `pre` and body `body`, and `P` calling `Q` after
    declaring a local type `tyName` and assuming it is a singleton. `tyName` is the name a
    transform generates for the type argument that the call does not determine. -/
def capturedLocalTypeProg (tyName : String) (pre : List Expression.Expr)
    (body : List Statement) : Program := { decls := [
  mkProc "Q" ["a"] [] [] body pre,
  mkProc "P" [] [] [] [
    .typeDecl { name := tyName, params := [] } .empty,
    Statement.assume "one" (singletonAll (.tcons tyName [])) .empty,
    callS "Q" []]] }

end Core.CallFixtures

end -- public section
end
