/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import Strata.Languages.Core.Logic.HoareCall
import Strata.Languages.Core.Logic.HoareTotal
import Strata.Languages.Core.Logic.HoareUnstructured
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Strata.DL.Imperative.StoreProps
import Strata.DL.Imperative.MetaDataProps

open Imperative
open StrataDDM (Program)

namespace Strata.HoarePolymorphicProcedureTest

open HoareUtils

/-- The program.  `Id<a>`, `IdInt` and `IdCfg<a>` copy their input `x` to their output `r`;
    `IdCfg` has a control-flow-graph body.  `Relay<b>`, `PolyToMono<b>`, `MonoToPoly` and
    `RelayCfg<b>` call one of them and copy its output into `s`.  `CallFirst<a>` calls the
    polymorphic function `first`. -/
private def polyPgm : Program :=
#strata
program Core;

procedure Id<a>(x : a, out r : a)
spec {
  ensures r == x;
}
{
  r := x;
};

procedure Relay<b>(y : b, out s : b)
spec {
  ensures s == y;
}
{
  call Id(y, out s);
};

procedure IdInt(x : int, out r : int)
spec {
  ensures r == x;
}
{
  r := x;
};

procedure PolyToMono<b>(z : b, y : int, out s : int)
spec {
  ensures s == y;
}
{
  call IdInt(y, out s);
};

procedure MonoToPoly(y : int, out s : int)
spec {
  ensures s == y;
}
{
  call Id(y, out s);
};

procedure IdCfg<a>(x : a, out r : a)
spec {
  ensures r == x;
}
cfg entry {
  entry: {
    r := x;
    return;
  }
};

procedure RelayCfg<b>(y : b, out s : b)
spec {
  ensures s == y;
}
{
  call IdCfg(y, out s);
};

function first<a>(x : a, y : a) : a {
  x
}

procedure CallFirst<a>(x : a, y : a, out r : a)
spec {
  ensures r == first(x, y);
}
{
  r := first(x, y);
};
#end

/-- The type-checked program: the type checker records on each call the type arguments at which
    it calls its callee (`some []` for the monomorphic `IdInt`). -/
def polyAST : Core.Program := typeCheckedAST polyPgm

/-! # Contracts of polymorphic procedures

Every procedure of `polyPgm` meets its contract under partial correctness
(`Procedure.contractTriple`) and total correctness (`Procedure.contractTripleTotal`).  For a
polymorphic procedure these say that every instance of the procedure
(`Core.Procedure.instantiateTypes`) meets the instantiated contract, so the proof works at an
arbitrary monotype `T`: `Core.Procedure.instantiateTypes_of_typeArgs_singleton` reduces an
instance of a procedure with one type parameter to its types substituted, which the
`*_subst` lemmas spell out with the shapes below.

The procedures come in three shapes, each a function of the type of the formals:
- `copyProc n T` (`Id`, `IdInt`) and `copyCfgProc n T` (`IdCfg`) copy `x : T` to `r : T` and
  ensure `r == x`;
- `relayProc n extra T callee tyArgs` (`Relay`, `PolyToMono`, `MonoToPoly`, `RelayCfg`) calls
  `callee` at `tyArgs` with `y : T` and `out s : T`, and ensures `s == y`;
- `callFirstProc T` (`CallFirst`) assigns `first(x, y)` to `r` and ensures `r == first(x, y)`.

The calls cover the combinations of a polymorphic or monomorphic caller and callee
(`Relay` → `Id`, `PolyToMono` → `IdInt`, `MonoToPoly` → `Id` at `int`) and a callee with a CFG
body (`RelayCfg` → `IdCfg`).  One proof of the call serves them all (`relay_call`,
`relay_call_total`): it takes the facts it needs about the callee (`CopyCallee`), which
`copyProc_*` and `copyCfg_*` prove for the two body kinds, and about the caller
(`RelayCaller`).  No proof rule exists yet for a total triple over a CFG, so `IdCfg`'s total
contract proves termination by following its three steps (`copyCfg_terminates`).  A value's
type is all the proofs
know about the values of the formals: the contract preconditions give each formal a value whose
sort is its declared type, and an equality of two such values evaluates to `true` exactly when
they are equal (`Core.eval_eq_tt_iff`).  `CallFirst` needs nothing about `first` but that a
call to it evaluates to a value of its result type (`Core.eval_app2_op_of_sort`), and that the
value depends only on the arguments.

The facts that bind the translated program to the shapes use `native_decide`: the translation
is `partial`, so the kernel cannot reduce it.

## Key results

Each procedure meets its contract under partial and total correctness:
`id_meets_contract`, `id_meets_contract_total`, `idInt_meets_contract`,
`idInt_meets_contract_total`, `idCfg_meets_contract`, `idCfg_meets_contract_total`,
`relay_meets_contract`, `relay_meets_contract_total`, `polyToMono_meets_contract`,
`polyToMono_meets_contract_total`, `monoToPoly_meets_contract`,
`monoToPoly_meets_contract_total`, `relayCfg_meets_contract`,
`relayCfg_meets_contract_total`, `callFirst_meets_contract` and
`callFirst_meets_contract_total`. -/

private abbrev π : String → Option Core.Procedure := polyAST.findProcByString?

private def xId : Core.Expression.Ident := ⟨"x", ()⟩
private def rId : Core.Expression.Ident := ⟨"r", ()⟩
private def yId : Core.Expression.Ident := ⟨"y", ()⟩
private def sId : Core.Expression.Ident := ⟨"s", ()⟩
private def zId : Core.Expression.Ident := ⟨"z", ()⟩

/-- The variable `x`, annotated with the type `T`. -/
private abbrev tv (x : Core.Expression.Ident) (T : Lambda.LMonoTy) : Core.Expression.Expr :=
  .fvar Core.valueLoc x (some T)

/-- `x == y`, at the type `T`. -/
private abbrev eqE (x y : Core.Expression.Ident) (T : Lambda.LMonoTy) : Core.Expression.Expr :=
  .eq Core.valueLoc (tv x T) (tv y T)

/-- `first(x, y)`, at the type `T`. -/
private abbrev firstE (T : Lambda.LMonoTy) : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc
    (.op Core.valueLoc ⟨"first", ()⟩ (some (.arrow T (.arrow T T)))) (tv xId T)) (tv yId T)

/-! ## The shapes of the procedures

The metadata the translation attaches to the clauses and statements is read off the translated
program, so that the shapes do not depend on where the program sits in this file.  The proofs
never inspect it. -/

/-- The metadata of the first postcondition of the procedure `n`. -/
private def postMdOf (n : String) : MetaData Core.Expression :=
  ((procOf polyAST n).spec.postconditions.toList.head?.map (·.2.md)).getD #[]

/-- The metadata of the first statement of the structured body of the procedure `n`, when it
    is a command. -/
private def cmdMdOf (n : String) : MetaData Core.Expression :=
  match bodyOf polyAST n with
  | .cmd (.cmd (.set _ _ md)) :: _ => md
  | .cmd (.call _ _ _ md) :: _ => md
  | _ => #[]

/-- The commands and transfer of the entry block of the CFG body of the procedure `n`. -/
private def entryBlockOf (n : String) :
    Option (List Core.Command × Imperative.DetTransferCmd String Core.Expression) :=
  match (procOf polyAST n).body with
  | .cfg c _ => (c.blocks.lookup "entry").map fun b => (b.cmds, b.transfer)
  | .structured _ _ => none
  | .abstract => none

/-- The metadata of the first command of the entry block of the procedure `n`. -/
private def cfgCmdMdOf (n : String) : MetaData Core.Expression :=
  match entryBlockOf n with
  | some (.cmd (.set _ _ md) :: _, _) => md
  | _ => #[]

/-- The metadata of the variable on the right-hand side of the first command of the entry block
    of the procedure `n`: the translation keeps the source locations of a CFG body's
    expressions. -/
private def cfgRhsMdOf (n : String) : Core.ExpressionMetadata :=
  match entryBlockOf n with
  | some (.cmd (.set _ (.det (.fvar m _ _)) _) :: _, _) => m
  | _ => Core.valueLoc

/-- The metadata of the transfer of the entry block of the procedure `n`. -/
private def cfgFinishMdOf (n : String) : MetaData Core.Expression :=
  match entryBlockOf n with
  | some (_, .finish md) => md
  | _ => #[]

/-- The signature of a copying procedure `n` at the type `T`: `x : T`, `out r : T`. -/
private def copyHeader (n : String) (T : Lambda.LMonoTy) : Core.Procedure.Header :=
  { name := ⟨n, ()⟩, typeArgs := [], inputs := [(xId, T)], outputs := [(rId, T)] }

/-- The contract of a copying procedure `n` at the type `T`: `ensures r == x`. -/
private def copySpec (n : String) (T : Lambda.LMonoTy) : Core.Procedure.Spec :=
  { preconditions := [],
    postconditions := [(n ++ "_ensures_0", { expr := eqE rId xId T, md := postMdOf n })] }

/-- The procedure `n` at the type `T` with a structured body `r := x`. -/
private def copyProc (n : String) (T : Lambda.LMonoTy) : Core.Procedure where
  header := copyHeader n T
  spec := copySpec n T
  body := .structured [Core.Statement.set rId (tv xId T) (cmdMdOf n)] false

/-- The command `r := x` of the CFG body of the procedure `n` at the type `T`. -/
private abbrev cfgSet (n : String) (T : Lambda.LMonoTy) : Core.Command :=
  .cmd (.set rId (.det (.fvar (cfgRhsMdOf n) xId (some T))) (cfgCmdMdOf n))

/-- The CFG body of the procedure `n` at the type `T`: one block `r := x; return`. -/
private def copyCfg (n : String) (T : Lambda.LMonoTy) : Core.DetCFG :=
  { entry := "entry",
    blocks := [("entry", { cmds := [cfgSet n T], transfer := .finish (cfgFinishMdOf n) })] }

/-- The procedure `n` at the type `T` with the CFG body `copyCfg n T`. -/
private def copyCfgProc (n : String) (T : Lambda.LMonoTy) : Core.Procedure where
  header := copyHeader n T
  spec := copySpec n T
  body := .cfg (copyCfg n T) false

/-- The arguments `(y, out s)` of a call, with `y` at the type `T`. -/
private abbrev relayArgs (T : Lambda.LMonoTy) : List (CallArg Core.Expression) :=
  [.inArg (tv yId T), .outArg sId]

/-- The procedure `n` with inputs `extra` and `y : T` and output `s : T`, whose body calls
    `callee` at `tyArgs` with `(y, out s)` and which ensures `s == y`. -/
private def relayProc (n : String) (extra : List (Core.Expression.Ident × Lambda.LMonoTy))
    (T : Lambda.LMonoTy) (callee : String) (tyArgs : Option (List Core.Expression.Ty)) :
    Core.Procedure where
  header := { name := ⟨n, ()⟩, typeArgs := [], inputs := extra ++ [(yId, T)],
              outputs := [(sId, T)] }
  spec := { preconditions := [],
            postconditions := [(n ++ "_ensures_0", { expr := eqE sId yId T, md := postMdOf n })] }
  body := .structured [Core.Statement.call callee tyArgs (relayArgs T) (cmdMdOf n)] false

/-- `CallFirst` at the type `T`: `r := first(x, y)`, ensuring `r == first(x, y)`. -/
private def callFirstProc (T : Lambda.LMonoTy) : Core.Procedure where
  header := { name := ⟨"CallFirst", ()⟩, typeArgs := [], inputs := [(xId, T), (yId, T)],
              outputs := [(rId, T)] }
  spec := { preconditions := [],
            postconditions := [("CallFirst_ensures_0",
              { expr := .eq Core.valueLoc (tv rId T) (firstE T), md := postMdOf "CallFirst" })] }
  body := .structured [Core.Statement.set rId (firstE T) (cmdMdOf "CallFirst")] false

/-- `p` with the type parameters `as`. -/
private abbrev withTypeArgs (p : Core.Procedure) (as : List String) : Core.Procedure :=
  { p with header := { p.header with typeArgs := as } }

/-! ### The translated procedures -/

/-- The procedure `Id` is `copyProc "Id"` at its type parameter `a`. -/
private theorem id_find : π "Id" = some (withTypeArgs (copyProc "Id" (.ftvar "a")) ["a"]) := by
  native_decide

/-- The procedure `Relay` calls `Id` at its type parameter `b`. -/
private theorem relay_find : π "Relay" =
    some (withTypeArgs (relayProc "Relay" [] (.ftvar "b") "Id" (some [.forAll [] (.ftvar "b")]))
      ["b"]) := by
  native_decide

/-- The procedure `IdInt` is `copyProc "IdInt"` at `int`. -/
private theorem idInt_find : π "IdInt" = some (copyProc "IdInt" .int) := by native_decide

/-- The procedure `PolyToMono` calls the monomorphic `IdInt`, without type arguments. -/
private theorem polyToMono_find : π "PolyToMono" =
    some (withTypeArgs (relayProc "PolyToMono" [(zId, .ftvar "b")] .int "IdInt" (some []))
      ["b"]) := by
  native_decide

/-- The procedure `MonoToPoly` calls `Id` at `int`. -/
private theorem monoToPoly_find : π "MonoToPoly" =
    some (relayProc "MonoToPoly" [] .int "Id" (some [.forAll [] .int])) := by
  native_decide

/-- The procedure `IdCfg` is `copyCfgProc "IdCfg"` at its type parameter `a`. -/
private theorem idCfg_find : π "IdCfg" =
    some (withTypeArgs (copyCfgProc "IdCfg" (.ftvar "a")) ["a"]) := by
  native_decide

/-- The procedure `RelayCfg` calls `IdCfg` at its type parameter `b`. -/
private theorem relayCfg_find : π "RelayCfg" =
    some (withTypeArgs
      (relayProc "RelayCfg" [] (.ftvar "b") "IdCfg" (some [.forAll [] (.ftvar "b")])) ["b"]) := by
  native_decide

/-- The procedure `CallFirst` is `callFirstProc` at its type parameter `a`. -/
private theorem callFirst_find : π "CallFirst" =
    some (withTypeArgs (callFirstProc (.ftvar "a")) ["a"]) := by
  native_decide

/-! ### Instances -/

/-- Mapping the types of `copyProc n T` maps `T`. -/
private theorem copyProc_mapTys (n : String) (T : Lambda.LMonoTy)
    (f : Lambda.LMonoTy → Lambda.LMonoTy) : (copyProc n T).mapTys f [] = copyProc n (f T) := by
  simp [Core.Procedure.mapTys, copyProc, copyHeader, copySpec, Core.mapStmtsTys,
    Core.mapCmdTys, Core.mapCmdWith, Lambda.mapExprTys, Lambda.LExpr.replaceUserProvidedType,
    Imperative.Block.mapExpr, Imperative.Stmt.mapExpr, Imperative.ExprOrNondet.map]

/-- Mapping the types of `copyCfgProc n T` maps `T`. -/
private theorem copyCfgProc_mapTys (n : String) (T : Lambda.LMonoTy)
    (f : Lambda.LMonoTy → Lambda.LMonoTy) :
    (copyCfgProc n T).mapTys f [] = copyCfgProc n (f T) := by
  simp [Core.Procedure.mapTys, copyCfgProc, copyCfg, copyHeader, copySpec,
    Core.DetCFG.mapCmdsGuards, Core.mapCmdTys, Core.mapCmdWith, Lambda.mapExprTys,
    Lambda.LExpr.replaceUserProvidedType, Imperative.ExprOrNondet.map,
    Imperative.MetaData.mapExprs_empty]

/-- Mapping the types of `relayProc n extra T callee tyArgs` maps `extra`, `T` and
    `tyArgs`. -/
private theorem relayProc_mapTys (n : String)
    (extra : List (Core.Expression.Ident × Lambda.LMonoTy))
    (T : Lambda.LMonoTy) (callee : String) (tyArgs : Option (List Core.Expression.Ty))
    (f : Lambda.LMonoTy → Lambda.LMonoTy) :
    (relayProc n extra T callee tyArgs).mapTys f [] =
      relayProc n (extra.map fun p => (p.1, f p.2)) (f T) callee
        (tyArgs.map (·.map (Lambda.mapLTyTys f))) := by
  simp [Core.Procedure.mapTys, relayProc, Core.mapStmtsTys, Core.mapCmdTys, Core.mapCmdWith,
    Lambda.mapExprTys, Lambda.LExpr.replaceUserProvidedType, Imperative.Block.mapExpr,
    Imperative.Stmt.mapExpr, Imperative.CallArg.mapInput]

/-- Substituting in the types of `callFirstProc T` substitutes in `T`. -/
private theorem callFirstProc_mapTys (T : Lambda.LMonoTy) (S : Lambda.Subst) :
    (callFirstProc T).mapTys (Lambda.LMonoTy.subst S) [] =
      callFirstProc (Lambda.LMonoTy.subst S T) := by
  simp [Core.Procedure.mapTys, callFirstProc, Core.mapStmtsTys, Core.mapCmdTys,
    Core.mapCmdWith, Lambda.mapExprTys, Lambda.LExpr.replaceUserProvidedType,
    Imperative.Block.mapExpr, Imperative.Stmt.mapExpr, Imperative.ExprOrNondet.map,
    Lambda.LMonoTy.arrow, Lambda.LMonoTy.subst_tcons, Lambda.LMonoTys.subst_eq_map, firstE, tv]

/-- Substituting `T` for `a` in `Id` gives `copyProc "Id" T`. -/
private theorem id_subst (T : Lambda.LMonoTy) :
    (withTypeArgs (copyProc "Id" (.ftvar "a")) ["a"]).mapTys
      (Lambda.LMonoTy.subst (Lambda.Subst.singleton "a" T)) [] = copyProc "Id" T := by
  erw [copyProc_mapTys, Lambda.LMonoTy.subst_singleton_self]

/-- A call to `Id` at `T` runs `copyProc "Id" T`. -/
private theorem id_callee (T : Lambda.LMonoTy) :
    Calls.typeInstantiatedCallee π "Id" (some [.forAll [] T]) = some (copyProc "Id" T) :=
  Core.Procedure.typeInstantiatedCallee_of_typeArgs_singleton id_find rfl rfl id_subst T

/-- Substituting `T` for `a` in `IdCfg` gives `copyCfgProc "IdCfg" T`. -/
private theorem idCfg_subst (T : Lambda.LMonoTy) :
    (withTypeArgs (copyCfgProc "IdCfg" (.ftvar "a")) ["a"]).mapTys
      (Lambda.LMonoTy.subst (Lambda.Subst.singleton "a" T)) [] = copyCfgProc "IdCfg" T := by
  erw [copyCfgProc_mapTys, Lambda.LMonoTy.subst_singleton_self]

/-- A call to `IdCfg` at `T` runs `copyCfgProc "IdCfg" T`. -/
private theorem idCfg_callee (T : Lambda.LMonoTy) :
    Calls.typeInstantiatedCallee π "IdCfg" (some [.forAll [] T]) =
      some (copyCfgProc "IdCfg" T) :=
  Core.Procedure.typeInstantiatedCallee_of_typeArgs_singleton idCfg_find rfl rfl idCfg_subst T

/-- A call to the monomorphic `IdInt` without type arguments runs it. -/
private theorem idInt_callee :
    Calls.typeInstantiatedCallee π "IdInt" (some []) = some (copyProc "IdInt" .int) :=
  (Core.Procedure.typeInstantiatedCallee_of_typeArgs_nil idInt_find rfl).2 ⟨rfl, rfl⟩

/-- Substituting `T` for `b` in `Relay` gives `Relay` calling `Id` at `T`. -/
private theorem relay_subst (T : Lambda.LMonoTy) :
    (withTypeArgs (relayProc "Relay" [] (.ftvar "b") "Id" (some [.forAll [] (.ftvar "b")]))
      ["b"]).mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton "b" T)) [] =
      relayProc "Relay" [] T "Id" (some [.forAll [] T]) := by
  erw [relayProc_mapTys]; simp [Lambda.mapLTyTys]

/-- Substituting `T` for `b` in `RelayCfg` gives `RelayCfg` calling `IdCfg` at `T`. -/
private theorem relayCfg_subst (T : Lambda.LMonoTy) :
    (withTypeArgs (relayProc "RelayCfg" [] (.ftvar "b") "IdCfg" (some [.forAll [] (.ftvar "b")]))
      ["b"]).mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton "b" T)) [] =
      relayProc "RelayCfg" [] T "IdCfg" (some [.forAll [] T]) := by
  erw [relayProc_mapTys]; simp [Lambda.mapLTyTys]

/-- Substituting `T` for `b` in `PolyToMono` gives `PolyToMono` with `z : T`, still calling
    `IdInt` at no type. -/
private theorem polyToMono_subst (T : Lambda.LMonoTy) :
    (withTypeArgs (relayProc "PolyToMono" [(zId, .ftvar "b")] .int "IdInt" (some []))
      ["b"]).mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton "b" T)) [] =
      relayProc "PolyToMono" [(zId, T)] .int "IdInt" (some []) := by
  erw [relayProc_mapTys]
  simp [Lambda.LMonoTy.subst_ground _ .int rfl]

/-- Substituting `T` for `a` in `CallFirst` gives `callFirstProc T`. -/
private theorem callFirst_subst (T : Lambda.LMonoTy) :
    (withTypeArgs (callFirstProc (.ftvar "a")) ["a"]).mapTys
      (Lambda.LMonoTy.subst (Lambda.Subst.singleton "a" T)) [] = callFirstProc T := by
  erw [callFirstProc_mapTys, Lambda.LMonoTy.subst_singleton_self]

/-! ## Values of a type -/

/-- A procedure whose postconditions are all `a == b` at the type `T` meets its postcondition
    at an environment pinned to a factory over `F` where `a` and `b` hold the same value of the
    runtime factory. -/
private theorem post_of_eq {F : Lambda.Factory Core.CoreLParams} {c : Core.Procedure}
    {a b : Core.Expression.Ident} {T : Lambda.LMonoTy}
    (hpost : ∀ lc ∈ c.spec.postconditions.toList, lc.2.expr = eqE a b T)
    {ρ : Env Core.Expression} (hpin : ρ.factory.factory = F) {v : Core.Expression.Val}
    (ha : ρ.store a = some v) (hb : ρ.store b = some v) (hv : HasVal.value ρ.factory v) :
    Core.Logic.Hoare.Procedure.contractPost F c ρ := by
  intro label check hmem _ _
  refine .inl ⟨hpin, ?_⟩
  change Core.Expression.eval ρ.factory ρ.store check.expr = some (HasBool.ttVal ρ.factory)
  rw [hpost _ hmem]
  exact Core.eval_eq_true _ (Core.eval_fvar _ ha hv) (Core.eval_fvar _ hb hv)

/-- A procedure with a postcondition `a == b` at the type `T`, at an environment pinned to a
    factory over `F` meeting its postcondition, where `a` and `b` hold values of the runtime
    factory of type `T`, has `a` and `b` hold the same value. -/
private theorem eq_of_post {F : Lambda.Factory Core.CoreLParams} {c : Core.Procedure}
    {a b : Core.Expression.Ident} {T : Lambda.LMonoTy}
    (hmem : ∃ lc ∈ c.spec.postconditions.toList,
      lc.2.attr = .Default ∧ lc.2.expr = eqE a b T)
    {ρ : Env Core.Expression} (hpin : ρ.factory.factory = F)
    (hpost : Core.Logic.Hoare.Procedure.contractPost F c ρ) {va vb : Core.Expression.Val}
    (ha : ρ.store a = some va) (hb : ρ.store b = some vb) (hva : HasVal.value ρ.factory va)
    (hvb : HasVal.value ρ.factory vb) (hta : Core.Logic.Hoare.Procedure.valueHasType T va)
    (htb : Core.Logic.Hoare.Procedure.valueHasType T vb) : va = vb := by
  obtain ⟨⟨label, check⟩, hlc, hattr, hexpr⟩ := hmem
  rcases hpost label check hlc hattr (someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store check.expr =
      some (HasBool.ttVal ρ.factory) at hex
    rw [hexpr] at hex
    exact (Core.eval_eq_tt_iff _ (Core.eval_fvar _ ha hva) (Core.eval_fvar _ hb hvb)
      (Lambda.LSort.toMonoTy_injective (hta.trans htb.symm))).1 hex
  · exact absurd hpin hne

/-! ## The copying procedures: `Id`, `IdInt` and `IdCfg` -/

/-- The clauses of `copyProc n T` type-check. -/
private theorem copyProc_checks (n : String) (T : Lambda.LMonoTy) :
    Core.Logic.Hoare.Procedure.contractChecksTyped (copyProc n T) := by
  simp [Core.Logic.Hoare.Procedure.contractChecksTyped, copyProc, copySpec, ListMap.toList,
    Lambda.LExpr.typeCheck, guard]

/-- The clauses of `copyCfgProc n T` type-check. -/
private theorem copyCfgProc_checks (n : String) (T : Lambda.LMonoTy) :
    Core.Logic.Hoare.Procedure.contractChecksTyped (copyCfgProc n T) := by
  simp [Core.Logic.Hoare.Procedure.contractChecksTyped, copyCfgProc, copySpec, ListMap.toList,
    Lambda.LExpr.typeCheck, guard]

/-- At an entry meeting the contract precondition of a procedure with the signature
    `copyHeader n T`, `x` holds a value of type `T`. -/
private theorem copy_input {F : Lambda.Factory Core.CoreLParams} {c : Core.Procedure}
    {n : String} {T : Lambda.LMonoTy} (hh : c.header = copyHeader n T) {ρ : Env Core.Expression}
    (hpre : Core.Logic.Hoare.Procedure.contractPre F c ρ) :
    ∃ vx, ρ.store xId = some vx ∧ Core.Logic.Hoare.Procedure.valueHasType T vx :=
  hpre.2.2.2.1 xId T (by rw [hh]; simp [copyHeader, ListMap.toList])

/-- At an entry meeting the contract precondition of a procedure with the signature
    `copyHeader n T`, `r` holds a value of type `T`. -/
private theorem copy_output {F : Lambda.Factory Core.CoreLParams} {c : Core.Procedure}
    {n : String} {T : Lambda.LMonoTy} (hh : c.header = copyHeader n T) {ρ : Env Core.Expression}
    (hpre : Core.Logic.Hoare.Procedure.contractPre F c ρ) :
    ∃ vr, ρ.store rId = some vr ∧ Core.Logic.Hoare.Procedure.valueHasType T vr :=
  hpre.2.2.2.2 rId T (by rw [hh]; simp [copyHeader, ListMap.toList])

/-- Every postcondition of a copying procedure is `r == x`. -/
private theorem copySpec_post (n : String) (T : Lambda.LMonoTy) :
    ∀ lc ∈ (copySpec n T).postconditions.toList, lc.2.expr = eqE rId xId T := by
  simp [copySpec, ListMap.toList]

/-- `r := x`, from an entry meeting the contract precondition of `copyProc n T` with a
    well-formed store, ends in its postcondition `r == x`. -/
private theorem copyProc_post_of_set {F : Lambda.Factory Core.CoreLParams} {n : String}
    {T : Lambda.LMonoTy} {ρ₀ : Env Core.Expression} {σ' : Core.CoreStore}
    {w : Core.Expression.Val}
    (hpre : Core.Logic.Hoare.Procedure.contractPre F (copyProc n T) ρ₀)
    (hwf : WellFormedStore ρ₀.store ρ₀.factory)
    (hev : Core.Expression.eval ρ₀.factory ρ₀.store (tv xId T) = some w)
    (hup : UpdateState Core.Expression ρ₀.store rId w σ') :
    Core.Logic.Hoare.Procedure.contractPost F (copyProc n T) { ρ₀ with store := σ' } := by
  obtain ⟨vx, hx, -⟩ := copy_input rfl hpre
  rw [Core.eval_fvar_of_wellFormedStore hwf, hx] at hev
  have hw : vx = w := Option.some.inj hev
  subst hw
  cases hup with
  | update _ hnew hother =>
    exact post_of_eq (copySpec_post n T) hpre.2.1 hnew ((hother xId (by decide)).trans hx)
      (hwf _ _ hx)

/-- **`copyProc n T`'s body meets its contract**: `r := x` ends with `r == x`. -/
private theorem copyProc_triple (n : String) (T : Lambda.LMonoTy)
    (F : Lambda.Factory Core.CoreLParams) (A : Env Core.Expression → Prop) :
    Core.Logic.Hoare.Triple π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre F (copyProc n T) ρ ∧ A ρ)
      [Stmt.block "" [Core.Statement.set rId (tv xId T) (cmdMdOf n)] #[]]
      (Core.Logic.Hoare.Procedure.contractPost F (copyProc n T)) (factory := F) := by
  refine Core.Logic.Hoare.block π testParams ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ rfl)
  refine Core.Logic.Hoare.of_storeWF_pre π testParams ?_
  exact Core.Logic.Hoare.set π testParams rId _ _ _ _
    fun ρ₀ σ' w ⟨⟨hpre, _⟩, hwf⟩ hev hup => copyProc_post_of_set hpre hwf hev hup

/-- **`copyProc n T`'s body meets its contract under total correctness**: `r := x` terminates
    and ends with `r == x`. -/
private theorem copyProc_triple_total (n : String) (T : Lambda.LMonoTy)
    (F : Lambda.Factory Core.CoreLParams) (A : Env Core.Expression → Prop) :
    Core.Logic.HoareTotal.Triple π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre F (copyProc n T) ρ ∧ A ρ)
      [Stmt.block "" [Core.Statement.set rId (tv xId T) (cmdMdOf n)] #[]]
      (Core.Logic.Hoare.Procedure.contractPost F (copyProc n T)) (factory := F) := by
  refine Core.Logic.HoareTotal.block π testParams ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ rfl)
  refine Core.Logic.HoareTotal.of_storeWF_pre π testParams ?_
  refine Core.Logic.HoareTotal.set π testParams rId _ _ _ _ (fun ρ₀ ⟨⟨hpre, _⟩, hwf⟩ _ => ?_)
    fun ρ₀ σ' w ⟨⟨hpre, _⟩, hwf⟩ hev hup => copyProc_post_of_set hpre hwf hev hup
  -- `r := x` can execute: `x` and `r` hold values of the type `T`.
  obtain ⟨vx, hx, htx⟩ := copy_input rfl hpre
  obtain ⟨vr, hr, htr⟩ := copy_output rfl hpre
  exact ⟨vx, (Core.eval_fvar_of_wellFormedStore hwf).trans hx, vr, .forAll [] T, hr,
    Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType (hwf _ _ hr) htr,
    Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType (hwf _ _ hx) htx⟩

/-- **`Id` meets its contract**: at every type, `r := x` ends with `r == x`. -/
theorem id_meets_contract : Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "Id" :=
  ⟨_, id_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl id_subst
    fun _ => ⟨copyProc_checks _ _, copyProc_triple _ _ _ _⟩⟩

/-- **`Id` meets its contract under total correctness**: at every type, `r := x` terminates
    and ends with `r == x`. -/
theorem id_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "Id" :=
  ⟨_, id_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl id_subst
    fun _ => ⟨copyProc_checks _ _, copyProc_triple_total _ _ _ _⟩⟩

/-- **`IdInt` meets its contract**: `r := x` ends with `r == x`. -/
theorem idInt_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "IdInt" :=
  ⟨_, idInt_find, Core.Procedure.forall_instance_of_typeArgs_nil rfl
    ⟨copyProc_checks _ _, copyProc_triple _ _ _ _⟩⟩

/-- **`IdInt` meets its contract under total correctness**: `r := x` terminates and ends with
    `r == x`. -/
theorem idInt_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "IdInt" :=
  ⟨_, idInt_find, Core.Procedure.forall_instance_of_typeArgs_nil rfl
    ⟨copyProc_checks _ _, copyProc_triple_total _ _ _ _⟩⟩

/-! ### `IdCfg`: a CFG body

A run of `copyCfg n T` from the entry store `σe` fetches the entry block, runs `r := x` and
finishes; `CfgInv` records what holds at each of these points. -/

/-- The configurations a run of `copyCfg n T` from the entry store `σe` at the runtime factory
    `fac` reaches, with what holds there: the store is `σe` until `r := x` runs, and afterwards
    `r` holds what `x` held in `σe`, `r` was bound in `σe`, and every other variable holds what
    it held in `σe`. -/
private inductive CfgInv (n : String) (T : Lambda.LMonoTy) (fac : Core.Expression.Factory)
    (σe : Core.CoreStore) : CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hs : ρ.store = σe) :
      CfgInv n T fac σe (.atBlock (copyCfg n T) "entry" ρ)
  | preSet (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hs : ρ.store = σe) :
      CfgInv n T fac σe
        (.inBlock (copyCfg n T) "entry" [cfgSet n T] (.finish (cfgFinishMdOf n)) ρ)
  | atFinish (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hre : (σe rId).isSome = true)
      (hr : ρ.store rId = σe xId) (hother : ∀ k, rId ≠ k → ρ.store k = σe k) :
      CfgInv n T fac σe (.inBlock (copyCfg n T) "entry" [] (.finish (cfgFinishMdOf n)) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hre : (σe rId).isSome = true)
      (hr : ρ.store rId = σe xId) (hother : ∀ k, rId ≠ k → ρ.store k = σe k) :
      CfgInv n T fac σe (.terminal ρ)

/-- The entry block of `copyCfg n T` is `r := x; return`. -/
private theorem copyCfg_lookup (n : String) (T : Lambda.LMonoTy) :
    (copyCfg n T).blocks.lookup "entry" =
      some { cmds := [cfgSet n T], transfer := .finish (cfgFinishMdOf n) } :=
  rfl

/-- `r := x` evaluates `x` to the value `x` holds, and runs only from a store where `r` is
    bound; afterwards `r` holds that value and every other variable is unchanged. -/
private theorem copySet_inv {π' : String → Option Core.Procedure} {m : Core.ExpressionMetadata}
    {ty : Option Lambda.LMonoTy} {md : MetaData Core.Expression} {fac : Core.Expression.Factory}
    {σ σ' : Core.CoreStore} {emitted : Trace Core.Expression}
    (h : Core.EvalCommandE π' fac σ (.cmd (.set rId (.det (.fvar m xId ty)) md)) σ' emitted) :
    (σ rId).isSome = true ∧ σ' rId = σ xId ∧ (∀ k, rId ≠ k → σ' k = σ k) ∧ emitted = [] := by
  obtain ⟨v, heval, ⟨old, _, hold, -⟩, hres, hother, rfl⟩ :=
    EvalCmdE.set_det_inv (evalCmdExtE_cmd_iff.mp h)
  obtain ⟨w, hw, hwtc⟩ := Lambda.LExpr.denoteEval_defines heval xId
    (by simp [Lambda.LExpr.LExpr.getVars])
  have hv : v = w := Option.some.inj (heval.symm.trans (Core.eval_fvar fac hw hwtc))
  subst hv
  exact ⟨by rw [hold]; rfl, hres.trans hw.symm, hother, rfl⟩

/-- One step of a run of `copyCfg n T` keeps `CfgInv` and emits no event. -/
private theorem cfgInv_step {π' : String → Option Core.Procedure} {n : String}
    {T : Lambda.LMonoTy} {fac : Core.Expression.Factory} {σe : Core.CoreStore}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)} (hinv : CfgInv n T fac σe before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π') before emitted after) :
    CfgInv n T fac σe after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf hs =>
    cases hstep with
    | fetch hlookup =>
      rw [copyCfg_lookup] at hlookup
      cases hlookup
      exact ⟨.preSet ρ hf hs, rfl⟩
  | preSet ρ hf hs =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨hre, hr, hother, rfl⟩ := copySet_inv hcmd
      rw [hs] at hre hr hother
      exact ⟨.atFinish _ hf hre hr hother, rfl⟩
  | atFinish ρ hf hre hr hother =>
    cases hstep with
    | finish => exact ⟨.terminal ρ hf hre hr hother, rfl⟩
  | terminal => cases hstep

/-- A run of `copyCfg n T` keeps `CfgInv` and emits no event. -/
private theorem cfgInv_run {π' : String → Option Core.Procedure} {n : String}
    {T : Lambda.LMonoTy} {fac : Core.Expression.Factory} {σe : Core.CoreStore}
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)} (hinv : CfgInv n T fac σe start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π')) start trace final) :
    CfgInv n T fac σe final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ _ _ _ _ hstep _ ih =>
    obtain ⟨hnext, rfl⟩ := cfgInv_step hinv hstep
    obtain ⟨hfinal, rfl⟩ := ih hnext
    exact ⟨hfinal, rfl⟩

/-- A store `σ'` where `r` holds what `x` held in `σe`, `r` was bound in `σe`, and every other
    variable holds what it held in `σe`, has these properties when projected through `σe`. -/
private theorem projectStore_copy {σe σ' : Core.CoreStore} (hre : (σe rId).isSome = true)
    (hr : σ' rId = σe xId) (hother : ∀ k, rId ≠ k → σ' k = σe k) :
    projectStore σe σ' rId = σe xId ∧ ∀ k, rId ≠ k → projectStore σe σ' k = σe k := by
  refine ⟨by simp [projectStore, hre, hr], fun k hk => ?_⟩
  unfold projectStore
  split
  · exact hother k hk
  · rename_i h; exact (Option.not_isSome_iff_eq_none.mp h).symm

/-- A finished run of `copyCfg n T` from the entry store `σe` ends, projected through `σe`,
    with `r` holding what `x` held in `σe`, every other variable holding what it held in `σe`,
    and its runtime factory, and emits no event. -/
private theorem copyCfg_finished {π' : String → Option Core.Procedure} {n : String}
    {T : Lambda.LMonoTy} {ρ₀ ρ' : Env Core.Expression} {trace : List (Event Core.Expression)}
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π'))
      (.atBlock (copyCfg n T) "entry" ρ₀) trace (.terminal ρ')) :
    projectStore ρ₀.store ρ'.store rId = ρ₀.store xId ∧
      (∀ k, rId ≠ k → projectStore ρ₀.store ρ'.store k = ρ₀.store k) ∧
      ρ'.factory = ρ₀.factory ∧ trace = [] := by
  obtain ⟨hfinal, rfl⟩ := cfgInv_run (CfgInv.atEntry ρ₀ rfl rfl) hrun
  cases hfinal with
  | terminal _ hf hre hr hother =>
    obtain ⟨hr', hother'⟩ := projectStore_copy hre hr hother
    exact ⟨hr', hother', hf, rfl⟩

/-- A run of `copyCfgProc n T`'s body from `σe` ends with `r` holding what `x` held in `σe` and
    every other variable holding what it held in `σe`. -/
private theorem copyCfg_run {n : String} {T : Lambda.LMonoTy} {fac : Core.Expression.Factory}
    {σe σEnd : Core.CoreStore} {evs : Trace Core.Expression}
    (hb : Core.CoreBodyExecE π (copyCfgProc n T).body ⟨σe, fac⟩ σEnd evs) :
    σEnd rId = σe xId ∧ ∀ k, rId ≠ k → σEnd k = σe k := by
  cases hb with
  | cfg hrun =>
    obtain ⟨hr, hother, -⟩ := copyCfg_finished hrun
    exact ⟨hr, hother⟩

/-- From every entry meeting the contract precondition of `copyCfgProc n T`, every run of
    `copyCfg n T` must terminate, with no assertion. -/
private theorem copyCfg_terminates (n : String) (T : Lambda.LMonoTy)
    (F : Lambda.Factory Core.CoreLParams) {ρ₀ : Env Core.Expression}
    (hpre : Core.Logic.Hoare.Procedure.contractPre F (copyCfgProc n T) ρ₀)
    (hwf : WellFormedStore ρ₀.store ρ₀.factory) (I : ConditionInterp Core.Expression)
    (w : I.World) :
    (Core.Logic.EventLang.coreCFG π).MustTerminateAndAssertsValid I w
      (.atBlock (copyCfg n T) "entry" ρ₀) := by
  obtain ⟨vx, hx, htx⟩ := copy_input rfl hpre
  obtain ⟨vr, hr, htr⟩ := copy_output rfl hpre
  -- `return` finishes.
  have hfin : ∀ ρ, (Core.Logic.EventLang.coreCFG π).MustTerminateAndAssertsValid I w
      (.inBlock (copyCfg n T) "entry" [] (.finish (cfgFinishMdOf n)) ρ) := fun ρ =>
    .step ⟨_, _, .finish⟩ (fun _ _ h => by cases h; simp [Trace.AssertionsHoldIn])
      (fun _ _ h _ => by cases h; exact .terminal _)
  -- `r := x` runs, from a store where `x` and `r` hold values of the type `T`.
  refine .step ⟨_, _, .fetch (copyCfg_lookup n T)⟩
    (fun _ _ h => by cases h; simp [Trace.AssertionsHoldIn]) (fun _ _ h _ => ?_)
  cases h with
  | fetch hlookup =>
    rw [copyCfg_lookup] at hlookup
    cases hlookup
    have hev : Core.Expression.eval ρ₀.factory ρ₀.store
        (.fvar (cfgRhsMdOf n) xId (some T)) = some vx :=
      (Core.eval_fvar_of_wellFormedStore hwf).trans hx
    refine .step ⟨_, _, .step_cmd (.cmd_sem (.eval_set hev (UpdateState.of_update hr)
      ⟨vr, .forAll [] T, hr,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType (hwf _ _ hr) htr,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType (hwf _ _ hx) htx⟩
      (Core.coreEvaluator_WellFormedSemanticEvalVar _)))⟩
      (fun _ _ h => by
        cases h with
        | step_cmd hcmd => obtain ⟨-, -, -, rfl⟩ := copySet_inv hcmd; simp [Trace.AssertionsHoldIn])
      (fun _ _ h _ => by cases h; exact hfin _)

/-- **`copyCfgProc n T`'s body meets its contract**: from every entry meeting the contract
    precondition, the CFG `r := x; return` ends, on the store projected through the entry
    store, with `r == x`. -/
private theorem copyCfg_triple (n : String) (T : Lambda.LMonoTy)
    (F : Lambda.Factory Core.CoreLParams) (A : Env Core.Expression → Prop)
    (ρEntry : Env Core.Expression) :
    Core.Logic.Hoare.TripleUnstructured π testParams
      (fun ρ => (Core.Logic.Hoare.Procedure.contractPre F (copyCfgProc n T) ρ ∧ A ρ) ∧
        ρ = ρEntry)
      (copyCfg n T)
      (fun ρ' => Core.Logic.Hoare.Procedure.contractPost F (copyCfgProc n T)
        { ρ' with store := projectStore ρEntry.store ρ'.store })
      (factory := F) := by
  intro ρ₀ ⟨⟨hpre, _⟩, hρ⟩ hinit
  subst hρ
  refine ⟨fun c trace hrun => (Trace.AssertionsValid_iff_assertionsHoldIn _ trace).2 fun w =>
    (copyCfg_terminates n T F hpre hinit.storeWellDefined _ w).assertionsHoldIn hrun,
    fun ρ' trace hterm _ => ?_⟩
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π))
      (.atBlock (copyCfg n T) "entry" ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  obtain ⟨hr, hother, hf, rfl⟩ := copyCfg_finished hrun
  obtain ⟨vx, hx, -⟩ := copy_input rfl hpre
  refine post_of_eq (copySpec_post n T) (by rw [hf]; exact hpre.2.1)
    (hr.trans hx) ((hother xId (by decide)).trans hx) ?_
  rw [hf]
  exact hinit.storeWellDefined _ _ hx

/-- **`copyCfgProc n T`'s body meets its contract under total correctness**: from every entry
    meeting the contract precondition, the CFG `r := x; return` terminates and ends, on the
    store projected through the entry store, with `r == x`. -/
private theorem copyCfg_triple_total (n : String) (T : Lambda.LMonoTy)
    (F : Lambda.Factory Core.CoreLParams) (A : Env Core.Expression → Prop)
    (ρEntry : Env Core.Expression) :
    Core.Logic.HoareTotal.TripleUnstructured π testParams
      (fun ρ => (Core.Logic.Hoare.Procedure.contractPre F (copyCfgProc n T) ρ ∧ A ρ) ∧
        ρ = ρEntry)
      (copyCfg n T)
      (fun ρ' => Core.Logic.Hoare.Procedure.contractPost F (copyCfgProc n T)
        { ρ' with store := projectStore ρEntry.store ρ'.store })
      (factory := F) :=
  fun ρ₀ hpre hinit =>
    ⟨fun w => copyCfg_terminates n T F hpre.1.1 hinit.storeWellDefined _ w,
      (copyCfg_triple n T F A ρEntry ρ₀ hpre hinit).2⟩

/-- **`IdCfg` meets its contract**: at every type, its CFG body ends with `r == x`. -/
theorem idCfg_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "IdCfg" :=
  ⟨_, idCfg_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl idCfg_subst
    fun _ => ⟨copyCfgProc_checks _ _, copyCfg_triple _ _ _ _⟩⟩

/-- **`IdCfg` meets its contract under total correctness**: at every type, its CFG body
    terminates and ends with `r == x`. -/
theorem idCfg_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "IdCfg" :=
  ⟨_, idCfg_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl idCfg_subst
    fun _ => ⟨copyCfgProc_checks _ _, copyCfg_triple_total _ _ _ _⟩⟩

/-! ## Calls: `Relay`, `PolyToMono`, `MonoToPoly` and `RelayCfg`

A call `(y, out s)` to a copying procedure enters it with `x` holding `y`'s value and `r`
holding `s`'s (`entryStore`), and copies the final `r` into `s`.  `relay_call` and
`relay_call_total` prove the call's triple once, from the facts about the callee that
`CopyCallee` collects and the facts about the caller that `RelayCaller` collects. -/

/-- The callee entry store of a call `(y, out s)` when `y` holds `vy` and `s` holds `vs`: `x`
    holds `vy`, `r` holds `vs`, and nothing else is bound. -/
private abbrev entryStore (vy vs : Core.Expression.Val) : Core.CoreStore :=
  SemanticStore.update (SemanticStore.update emptyStore xId vy) rId vs

/-- In `entryStore vy vs`, `x` holds `vy`. -/
private theorem entryStore_x (vy vs : Core.Expression.Val) : entryStore vy vs xId = some vy := by
  simp [SemanticStore.update, xId, rId]

/-- In `entryStore vy vs`, `r` holds `vs`. -/
private theorem entryStore_r (vy vs : Core.Expression.Val) : entryStore vy vs rId = some vs := by
  simp [SemanticStore.update]

/-- `entryStore vy vs` is a well-formed store when `vy` and `vs` are values of the factory. -/
private theorem entryStore_wf {fac : Core.Expression.Factory} {vy vs : Core.Expression.Val}
    (hvy : HasVal.value fac vy) (hvs : HasVal.value fac vs) :
    WellFormedStore (entryStore vy vs) fac := by
  intro k w hk
  simp only [SemanticStore.update] at hk
  split at hk
  · cases hk; exact hvs
  · split at hk
    · cases hk; exact hvy
    · simp [emptyStore] at hk

/-- The facts the call proofs need of the callee `c` that a call to `cn` at `tyArgs` runs: it
    has the signature and contract of a copying procedure at `T`, its contract is proved, its
    procedure sees `Core.Factory` and no axiom, every run of its body copies `x` into `r` and
    changes nothing else, and from the entry store of a call its body's gate holds and some run
    of it finishes. -/
private structure CopyCallee (cn : String) (tyArgs : Option (List Core.Expression.Ty))
    (c : Core.Procedure) (T : Lambda.LMonoTy) : Prop where
  callee : Calls.typeInstantiatedCallee π cn tyArgs = some c
  header : c.header = copyHeader cn T
  spec : c.spec = copySpec cn T
  contract : Core.Logic.Hoare.Procedure.contractTriple polyAST testParams cn
  factory : polyAST.factoryBeforeProcedure cn = Core.Factory
  axioms : ∀ ρ, Core.Specification.AxiomsBeforeProcedureDecl cn polyAST ρ
  run : ∀ fac σe σEnd evs, Core.CoreBodyExecE π c.body ⟨σe, fac⟩ σEnd evs →
    σEnd rId = σe xId ∧ ∀ k, rId ≠ k → σEnd k = σe k
  gate : ∀ (fac : Core.Expression.Factory) vy vs, fac.factory = Core.Factory →
    HasVal.value fac vy → HasVal.value fac vs →
    Core.Logic.Hoare.Procedure.valueHasType T vy → Core.Logic.Hoare.Procedure.valueHasType T vs →
    match c.body with
    | .structured bss _ =>
        Core.Logic.BlockInitEnvWF testParams [Stmt.block "" bss #[]] ⟨entryStore vy vs, fac⟩
    | .cfg cfg _ => Core.Logic.CFGInitEnvWF testParams cfg ⟨entryStore vy vs, fac⟩
    | .abstract => True
  finishes : ∀ (fac : Core.Expression.Factory) vy vs, fac.factory = Core.Factory →
    HasVal.value fac vy → HasVal.value fac vs →
    Core.Logic.Hoare.Procedure.valueHasType T vy → Core.Logic.Hoare.Procedure.valueHasType T vs →
    ∃ σEnd evs, Core.CoreBodyExecE π c.body ⟨entryStore vy vs, fac⟩ σEnd evs
  transparent : c.body.isOpaque = Bool.false

/-- The facts the call proofs need of the caller `cp`, a procedure named `pn`: it sees
    `Core.Factory`, has an input `y : T` and an output `s : T`, and ensures `s == y`. -/
private structure RelayCaller (pn : String) (cp : Core.Procedure) (T : Lambda.LMonoTy) :
    Prop where
  factory : polyAST.factoryBeforeProcedure pn = Core.Factory
  input : (yId, T) ∈ cp.header.inputs.toList
  output : (sId, T) ∈ cp.header.outputs.toList
  post : ∀ lc ∈ cp.spec.postconditions.toList, lc.2.expr = eqE sId yId T

/-- The precondition of the body of the caller `cp` named `pn`: its contract precondition,
    the axioms it sees and a well-formed store. -/
private abbrev CallerPre (pn : String) (cp : Core.Procedure) (ρ : Env Core.Expression) : Prop :=
  (Core.Logic.Hoare.Procedure.contractPre (polyAST.factoryBeforeProcedure pn) cp ρ ∧
    Core.Specification.AxiomsBeforeProcedureDecl pn polyAST ρ) ∧
    WellFormedStore ρ.store ρ.factory

/-- At an entry of a caller meeting `CallerPre`, the runtime factory is over `Core.Factory`
    and `y` and `s` hold values of type `T`. -/
private theorem caller_values {pn : String} {cp : Core.Procedure} {T : Lambda.LMonoTy}
    (hcaller : RelayCaller pn cp T) {ρ : Env Core.Expression} (h : CallerPre pn cp ρ) :
    ρ.factory.factory = Core.Factory ∧
      (∃ vy, ρ.store yId = some vy ∧ HasVal.value ρ.factory vy ∧
        Core.Logic.Hoare.Procedure.valueHasType T vy) ∧
      (∃ vs, ρ.store sId = some vs ∧ HasVal.value ρ.factory vs ∧
        Core.Logic.Hoare.Procedure.valueHasType T vs) := by
  obtain ⟨⟨hpre, _⟩, hwf⟩ := h
  obtain ⟨vy, hy, hty⟩ := hpre.2.2.2.1 yId T hcaller.input
  obtain ⟨vs, hs, hts⟩ := hpre.2.2.2.2 sId T hcaller.output
  exact ⟨hpre.2.1.trans hcaller.factory, ⟨vy, hy, hwf _ _ hy, hty⟩, ⟨vs, hs, hwf _ _ hs, hts⟩⟩

/-- The callee entry store of a call `(y, out s)` to a procedure with the signature
    `copyHeader cn T` is `entryStore vy vs`, where `y` holds `vy` and `s` holds `vs`. -/
private theorem callEntry_inv {c : Core.Procedure} {cn : String} {T : Lambda.LMonoTy}
    (hh : c.header = copyHeader cn T) {fac : Core.Expression.Factory} {σ σAO : Core.CoreStore}
    (hwf : WellFormedStore σ fac) (h : Core.CallEntry fac σ c (relayArgs T) σAO) :
    ∃ vy vs, σ yId = some vy ∧ σ sId = some vs ∧ σAO = entryStore vy vs := by
  obtain ⟨inputVals, outOnlyVals, hEE, hRV, σA, σIO, hIA, hIO, hSnap⟩ := h
  rw [show Calls.getInputExprs (relayArgs T) = [tv yId T] from rfl] at hEE
  rw [show CallArg.getOutArgs (relayArgs T) = [sId] from rfl] at hRV
  rw [show ProcedureHeader.inputParams (P := Core.Expression) c.header = [xId] by
    rw [hh]; rfl] at hIA
  rw [show Calls.outputOnlyParams (P := Core.Expression) c.header = [rId] by
    rw [hh]; rfl] at hIO
  rw [show Calls.inoutParams (P := Core.Expression) c.header = [] by rw [hh]; rfl] at hSnap
  cases hEE with
  | eval_some _ hey hEE2 =>
    cases hEE2
    rw [Core.eval_fvar_of_wellFormedStore hwf] at hey
    cases hRV with
    | read_some hs _ hRV2 =>
      cases hRV2
      cases hIA with
      | init_some hix hIA2 =>
        cases hIA2
        cases hIO with
        | init_some hir hIO2 =>
          cases hIO2
          refine ⟨_, _, hey, hs, ?_⟩
          rw [hSnap]
          funext k
          cases hix with
          | init _ hnewx hotherx =>
            cases hir with
            | init _ hnewr hotherr =>
              simp only [Calls.withOldSnapshots, List.find?_nil, SemanticStore.update]
              by_cases hkr : k = rId
              · subst hkr; simpa using hnewr
              · rw [ite_eq_right hkr, hotherr k (Ne.symm hkr)]
                by_cases hkx : k = xId
                · subst hkx; simpa using hnewx
                · rw [ite_eq_right hkx]; exact hotherx k (Ne.symm hkx)

/-- From an entry where `y` holds `vy` and `s` holds `vs`, a call `(y, out s)` to a procedure
    with the signature `copyHeader cn T` has the callee entry store `entryStore vy vs`. -/
private theorem callEntry_of {c : Core.Procedure} {cn : String} {T : Lambda.LMonoTy}
    (hh : c.header = copyHeader cn T) {fac : Core.Expression.Factory} {σ : Core.CoreStore}
    {vy vs : Core.Expression.Val} (hwf : WellFormedStore σ fac) (hy : σ yId = some vy)
    (hs : σ sId = some vs) :
    Core.CallEntry fac σ c (relayArgs T) (entryStore vy vs) := by
  refine ⟨[vy], [vs], .eval_some (fun k hk => ?_)
    ((Core.eval_fvar_of_wellFormedStore hwf).trans hy) .eval_none,
    .read_some hs (hwf _ _ hs) .read_none, SemanticStore.update emptyStore xId vy,
    entryStore vy vs, ?_, ?_, ?_⟩
  · simp only [HasFvars.getFvars, Lambda.LExpr.LExpr.getVars, List.mem_singleton] at hk
    subst hk; rw [hy]; rfl
  · rw [show ProcedureHeader.inputParams (P := Core.Expression) c.header = [xId] by
      rw [hh]; rfl]
    exact .init_some (InitState.of_update rfl) .init_none
  · rw [show Calls.outputOnlyParams (P := Core.Expression) c.header = [rId] by rw [hh]; rfl]
    exact .init_some (InitState.of_update (by simp [SemanticStore.update, emptyStore, xId, rId]))
      .init_none
  · rw [show Calls.inoutParams (P := Core.Expression) c.header = [] by rw [hh]; rfl]; rfl

/-- At the callee entry `entryStore vy vs`, for values `vy` and `vs` of type `T`, the callee's
    contract precondition holds. -/
private theorem callee_pre {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} {T : Lambda.LMonoTy} (hc : CopyCallee cn tyArgs c T)
    {fac : Core.Expression.Factory} (hfac : fac.factory = Core.Factory)
    {vy vs : Core.Expression.Val} (hty : Core.Logic.Hoare.Procedure.valueHasType T vy)
    (hts : Core.Logic.Hoare.Procedure.valueHasType T vs) :
    Core.Logic.Hoare.Procedure.contractPre (polyAST.factoryBeforeProcedure cn) c
      ⟨entryStore vy vs, fac⟩ := by
  refine ⟨?_, hfac.trans hc.factory.symm, ?_, ?_, ?_⟩
  · intro label check hmem; rw [hc.spec] at hmem; simp [copySpec, ListMap.toList] at hmem
  · intro k hk; rw [hc.header] at hk
    simp [copyHeader, Core.Procedure.Header.getInoutParams, Core.getInoutParams, ListMap.keys,
      xId, rId] at hk
  · intro k ty hmem
    rw [hc.header] at hmem
    simp only [copyHeader, ListMap.toList, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨vy, entryStore_x vy vs, hty⟩
  · intro k ty hmem
    rw [hc.header] at hmem
    simp only [copyHeader, ListMap.toList, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨vs, entryStore_r vy vs, hts⟩

/-- Every run of the callee writes only its output `r`. -/
private theorem callee_frame {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} {T : Lambda.LMonoTy} (hc : CopyCallee cn tyArgs c T) :
    ∀ proc, Calls.typeInstantiatedCallee π cn tyArgs = some proc →
      Core.Logic.Hoare.Procedure.bodyFrame π proc := by
  intro proc hlk
  obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
  intro σe fac σx evs hbody
  have hother := (hc.run _ _ _ _ hbody).2
  show invStoresExcept σe σx (ListMap.keys proc.header.outputs)
  rw [hc.header]
  exact invStoresExcept_of_agree fun k hk =>
    (hother k fun h => hk (by simp [copyHeader, ListMap.keys, h])).symm

/-- Every run of the callee leaves its output `r` holding a value of type `T`. -/
private theorem callee_outputs {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} {T : Lambda.LMonoTy} (hc : CopyCallee cn tyArgs c T) :
    ∀ proc, Calls.typeInstantiatedCallee π cn tyArgs = some proc →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped (polyAST.factoryBeforeProcedure cn) π proc := by
  intro proc hlk
  obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
  intro σe fac σx evs _ hin hbody
  obtain ⟨vx, hx, htx⟩ := hin xId T (by rw [hc.header]; simp [copyHeader, ListMap.toList])
  intro k ty hmem
  rw [hc.header] at hmem
  simp only [copyHeader, ListMap.toList, List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact ⟨vx, (hc.run _ _ _ _ hbody).1.trans hx, htx⟩

/-- **The call's write-back establishes the caller's postcondition `s == y`.**  The callee's
    postcondition gives `r == x` at its exit, `x` still holds `y`'s value there, and the call
    copies `r` into `s`. -/
private theorem caller_post {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} {T : Lambda.LMonoTy} (hc : CopyCallee cn tyArgs c T) {pn : String}
    {cp : Core.Procedure} (hcaller : RelayCaller pn cp T) {ρ₀ ρ' : Env Core.Expression}
    {σ' σAO : Core.CoreStore} (hpre : CallerPre pn cp ρ₀)
    (hpost : Core.Logic.Hoare.Procedure.contractPost (polyAST.factoryBeforeProcedure cn) c ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate c ρ')
    (hρ' : ρ'.factory = ρ₀.factory)
    (hce : Core.CallEntry ρ₀.factory ρ₀.store c (relayArgs T) σAO)
    (hframe : Core.Logic.Hoare.Procedure.storeFrame c σAO ρ'.store)
    (hcx : Core.CallExit ρ₀.factory ρ₀.store c (relayArgs T) ρ'.store σ') :
    Core.Logic.Hoare.Procedure.contractPost (polyAST.factoryBeforeProcedure pn) cp
      { ρ₀ with store := σ' } := by
  obtain ⟨hfac, ⟨vy, hy, hvy, hty⟩, -⟩ := caller_values hcaller hpre
  obtain ⟨vy', vs, hy', hs, rfl⟩ := callEntry_inv hc.header hpre.2 hce
  have e : vy = vy' := Option.some.inj (hy.symm.trans hy')
  subst e
  -- `x` still holds `vy` at the callee's exit.
  have hx : ρ'.store xId = some vy := by
    have h := hframe [xId] (fun a ha hb => by
      simp only [List.mem_singleton] at ha
      subst ha; rw [hc.header] at hb; simp [copyHeader, ListMap.keys, xId, rId] at hb)
      xId xId (by simp)
    exact h.symm.trans (entryStore_x _ _)
  -- The call writes back the value `r` holds into `s`.
  obtain ⟨_, outputVals, hRV, hUpd, -⟩ := hcx
  rw [show ProcedureHeader.outputParams (P := Core.Expression) c.header = [rId] by
    rw [hc.header]; rfl] at hRV
  rw [show CallArg.getLhs (relayArgs T) = [sId] from rfl] at hUpd
  cases hRV with
  | read_some hr hvr hRV2 =>
    cases hRV2
    cases hUpd with
    | update_some hu hUpd2 =>
      cases hUpd2
      cases hu with
      | update _ hnew hother =>
        -- The callee's postcondition `r == x` makes `r` hold `vy` too.
        obtain ⟨vr, hr', htr⟩ := hout rId T (by rw [hc.header]; simp [copyHeader, ListMap.toList])
        have e := Option.some.inj (hr'.symm.trans hr)
        subst e
        have hvrx : vr = vy :=
          eq_of_post ⟨(cn ++ "_ensures_0", { expr := eqE rId xId T, md := postMdOf cn }),
              by rw [hc.spec]; simp [copySpec, ListMap.toList], rfl, rfl⟩
            (by rw [hρ', hfac, hc.factory]) hpost hr hx (by rw [hρ']; exact hvr)
            (by rw [hρ']; exact hvy) htr hty
        subst hvrx
        exact post_of_eq hcaller.post (hfac.trans hcaller.factory.symm) hnew
          ((hother yId (by decide)).trans hy) hvy

/-- **A call `(y, out s)` to a copying callee ends in the caller's postcondition `s == y`**, by
    the callee's contract. -/
private theorem relay_call {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} {T : Lambda.LMonoTy} (hc : CopyCallee cn tyArgs c T) {pn : String}
    {cp : Core.Procedure} (hcaller : RelayCaller pn cp T) (md : MetaData Core.Expression) :
    Core.Logic.Hoare.Triple π testParams (CallerPre pn cp)
      [Core.Statement.call cn tyArgs (relayArgs T) md]
      (Core.Logic.Hoare.Procedure.contractPost (polyAST.factoryBeforeProcedure pn) cp)
      (factory := polyAST.factoryBeforeProcedure pn) := by
  have hF : polyAST.factoryBeforeProcedure pn = polyAST.factoryBeforeProcedure cn := by
    rw [hcaller.factory, hc.factory]
  rw [hF]
  refine Core.Logic.Hoare.Procedure.call_of_contract polyAST testParams cn (relayArgs T) md
    (CallerPre pn cp) _ hc.contract (callee_frame hc) (callee_outputs hc) ?_
    (fun _ _ _ _ _ _ _ => hc.axioms _) ?_
  · intro ρ₀ proc σAO hpre _ hlk hce
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    obtain ⟨hfac, ⟨vy, hy, hvy, hty⟩, ⟨vs, hs, hvs, hts⟩⟩ := caller_values hcaller hpre
    obtain ⟨vy', vs', hy', hs', rfl⟩ := callEntry_inv hc.header hpre.2 hce
    have e₁ : vy = vy' := Option.some.inj (hy.symm.trans hy')
    have e₂ : vs = vs' := Option.some.inj (hs.symm.trans hs')
    subst e₁ e₂
    refine ⟨callee_pre hc hfac hty hts, ?_⟩
    simp only [hc.transparent, Bool.false_eq_true, ↓reduceIte]
    exact hc.gate _ _ _ hfac hvy hvs hty hts
  · intro ρ₀ proc ρ' σ' σAO hpre _ hlk hpost hout hρ' hce hframe hcx
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    rw [← hF]
    exact caller_post hc hcaller hpre hpost hout hρ' hce hframe hcx

/-- **A call `(y, out s)` to a copying callee terminates in the caller's postcondition
    `s == y`**: the call has a callee entry, some run of the callee's body finishes from it, and
    the call writes `r` back into `s`. -/
private theorem relay_call_total {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} {T : Lambda.LMonoTy} (hc : CopyCallee cn tyArgs c T) {pn : String}
    {cp : Core.Procedure} (hcaller : RelayCaller pn cp T) (md : MetaData Core.Expression) :
    Core.Logic.HoareTotal.Triple π testParams (CallerPre pn cp)
      [Core.Statement.call cn tyArgs (relayArgs T) md]
      (Core.Logic.Hoare.Procedure.contractPost (polyAST.factoryBeforeProcedure pn) cp)
      (factory := polyAST.factoryBeforeProcedure pn) := by
  have hF : polyAST.factoryBeforeProcedure pn = polyAST.factoryBeforeProcedure cn := by
    rw [hcaller.factory, hc.factory]
  rw [hF]
  refine Core.Logic.HoareTotal.Procedure.call_of_contract polyAST testParams cn (relayArgs T) md
    (CallerPre pn cp) _ hc.contract ⟨_, hc.callee⟩ (callee_frame hc) (callee_outputs hc) ?_
    (fun _ _ _ _ _ _ _ => hc.axioms _) ?_ ?_ ?_ ?_
    (fun _ _ _ _ _ hlk ho _ => by
      obtain rfl := Option.some.inj (hlk.symm.trans hc.callee); rw [hc.transparent] at ho; cases ho)
  · -- hentry: the callee entry meets the callee's contract precondition and its body's gate.
    intro ρ₀ proc σAO hpre _ hlk hce
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    obtain ⟨hfac, ⟨vy, hy, hvy, hty⟩, ⟨vs, hs, hvs, hts⟩⟩ := caller_values hcaller hpre
    obtain ⟨vy', vs', hy', hs', rfl⟩ := callEntry_inv hc.header hpre.2 hce
    have e₁ : vy = vy' := Option.some.inj (hy.symm.trans hy')
    have e₂ : vs = vs' := Option.some.inj (hs.symm.trans hs')
    subst e₁ e₂
    refine ⟨callee_pre hc hfac hty hts, ?_⟩
    simp only [hc.transparent, Bool.false_eq_true, ↓reduceIte]
    exact hc.gate _ _ _ hfac hvy hvs hty hts
  · -- hexit: the write-back establishes the caller's postcondition.
    intro ρ₀ proc ρ' σ' σAO hpre _ hlk hpost hout hρ' hce hframe hcx
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    rw [← hF]
    exact caller_post hc hcaller hpre hpost hout hρ' hce hframe hcx
  · -- hcallEntry: the call has a callee entry store.
    intro ρ₀ proc hpre _ hlk
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    obtain ⟨-, ⟨vy, hy, -⟩, ⟨vs, hs, -⟩⟩ := caller_values hcaller hpre
    exact ⟨_, callEntry_of hc.header hpre.2 hy hs⟩
  · -- hbodyRun: some run of the callee's body finishes from the callee entry.
    intro ρ₀ proc σAO hpre _ hlk _ hce
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    obtain ⟨hfac, ⟨vy, hy, hvy, hty⟩, ⟨vs, hs, hvs, hts⟩⟩ := caller_values hcaller hpre
    obtain ⟨vy', vs', hy', hs', rfl⟩ := callEntry_inv hc.header hpre.2 hce
    have e₁ : vy = vy' := Option.some.inj (hy.symm.trans hy')
    have e₂ : vs = vs' := Option.some.inj (hs.symm.trans hs')
    subst e₁ e₂
    exact hc.finishes _ _ _ hfac hvy hvs hty hts
  · -- hcallExit: every finished run of the callee's body leaves `r` holding `y`'s value,
    -- which the call writes back into `s`.
    intro ρ₀ proc σAO σEnd bodyEvents hpre _ hlk hce hb
    obtain rfl : proc = c := Option.some.inj (hlk.symm.trans hc.callee)
    obtain ⟨-, ⟨vy, hy, hvy, hty⟩, ⟨vs, hs, hvs, hts⟩⟩ := caller_values hcaller hpre
    obtain ⟨vy', vs', hy', hs', rfl⟩ := callEntry_inv hc.header hpre.2 hce
    have e₁ : vy = vy' := Option.some.inj (hy.symm.trans hy')
    subst e₁
    have hr : σEnd rId = some vy := (hc.run _ _ _ _ hb).1.trans (entryStore_x _ _)
    refine ⟨SemanticStore.update ρ₀.store sId vy, by simp [CallArg.getLhs], [vy], ?_, ?_, ?_⟩
    · rw [show ProcedureHeader.outputParams (P := Core.Expression) proc.header = [rId] by
        rw [hc.header]; rfl]
      exact .read_some hr hvy .read_none
    · exact .update_some (UpdateState.of_update hs) .update_none
    · exact .cons ⟨vs, .forAll [] T, hs,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvs hts,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvy hty⟩ .nil

/-! ### The callees -/

/-- A run of `copyProc n T`'s body from `σe` ends with `r` holding what `x` held in `σe` and
    every other variable holding what it held in `σe`. -/
private theorem copyProc_run {n : String} {T : Lambda.LMonoTy} {fac : Core.Expression.Factory}
    {σe σEnd : Core.CoreStore} {evs : Trace Core.Expression}
    (hb : Core.CoreBodyExecE π (copyProc n T).body ⟨σe, fac⟩ σEnd evs) :
    σEnd rId = σe xId ∧ ∀ k, rId ≠ k → σEnd k = σe k := by
  obtain ⟨σCmd, hcmd, rfl⟩ := Core.CoreBodyExecE.singleton_cmd_invert hb
  obtain ⟨hre, hr, hother, -⟩ := copySet_inv hcmd
  exact projectStore_copy hre hr hother

/-- At the callee entry `entryStore vy vs` over `Core.Factory`, for values `vy` and `vs` of
    type `T`, the gate of `copyProc n T`'s body holds. -/
private theorem copyProc_gate {n : String} {T : Lambda.LMonoTy} {fac : Core.Expression.Factory}
    (hfac : fac.factory = Core.Factory) {vy vs : Core.Expression.Val}
    (hvy : HasVal.value fac vy) (hvs : HasVal.value fac vs)
    (hty : Core.Logic.Hoare.Procedure.valueHasType T vy) :
    Core.Logic.BlockInitEnvWF testParams
      [Stmt.block "" [Core.Statement.set rId (tv xId T) (cmdMdOf n)] #[]]
      ⟨entryStore vy vs, fac⟩ := by
  have hreads : HasVarsImp.readVars (P := Core.Expression)
      (CmdExt.cmd (Cmd.set rId (.det (tv xId T)) (cmdMdOf n))) = [xId] := rfl
  have htyped : HasTypedVarsImp.typedReadVars (P := Core.Expression)
      (CmdExt.cmd (Cmd.set rId (.det (tv xId T)) (cmdMdOf n))) = [(xId, .forAll [] T)] := rfl
  refine setBlockWF rId (tv xId T) (cmdMdOf n) _ hfac (entryStore_wf hvy hvs) (fun k hk => ?_)
    (show (entryStore vy vs rId).isSome = true by rw [entryStore_r]; rfl)
    ⟨fun k => if k = xId then some (.forAll [] T) else none, fun k ty hk => ?_,
      fun k ty hk => ?_⟩
  · rw [hreads, List.mem_singleton] at hk
    subst hk
    show (entryStore vy vs xId).isSome = true
    rw [entryStore_x]; rfl
  · by_cases h : k = xId
    · subst h
      simp only [ite_true, Option.some.injEq] at hk
      subst hk
      exact ⟨vy, entryStore_x vy vs,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvy hty⟩
    · simp [h] at hk
  · rw [htyped, List.mem_singleton, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp

/-- From the callee entry `entryStore vy vs`, for values `vy` and `vs` of type `T`, the body
    `r := x` of `copyProc n T` runs. -/
private theorem copyProc_finishes {n : String} {T : Lambda.LMonoTy}
    {fac : Core.Expression.Factory} {vy vs : Core.Expression.Val}
    (hvy : HasVal.value fac vy) (hvs : HasVal.value fac vs)
    (hty : Core.Logic.Hoare.Procedure.valueHasType T vy)
    (hts : Core.Logic.Hoare.Procedure.valueHasType T vs) :
    ∃ σEnd evs, Core.CoreBodyExecE π (copyProc n T).body ⟨entryStore vy vs, fac⟩ σEnd evs :=
  ⟨_, _, Core.CoreBodyExecE.singleton_cmd (.cmd_sem (.eval_set
    ((Core.eval_fvar_of_wellFormedStore (entryStore_wf hvy hvs)).trans (entryStore_x vy vs))
    (UpdateState.of_update (entryStore_r vy vs))
    ⟨vs, .forAll [] T, entryStore_r vy vs,
      Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvs hts,
      Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvy hty⟩
    (Core.coreEvaluator_WellFormedSemanticEvalVar _)))⟩

/-- At the callee entry `entryStore vy vs` over `Core.Factory`, for values `vy` and `vs`, the
    gate of `copyCfg n T` holds: it reads and writes only `x` and `r`, which the entry binds,
    and declares nothing. -/
private theorem copyCfg_gate {n : String} {T : Lambda.LMonoTy} {fac : Core.Expression.Factory}
    (hfac : fac.factory = Core.Factory) {vy vs : Core.Expression.Val}
    (hvy : HasVal.value fac vy) (hvs : HasVal.value fac vs) :
    Core.Logic.CFGInitEnvWF testParams (copyCfg n T) ⟨entryStore vy vs, fac⟩ where
  toWellFormedSemanticEval := Core.coreFactory_WellFormedSemanticEval _ hfac
  storeWellDefined := entryStore_wf hvy hvs
  readWritesDefined := by
    intro k hk _
    have hvars : HasVarsImp.modifiedVars (P := Core.Expression) (copyCfg n T) ++
        HasVarsImp.definedVars (P := Core.Expression) (copyCfg n T) false ++
        HasVarsImp.readVars (P := Core.Expression) (copyCfg n T) = [rId, xId] := rfl
    rw [hvars] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · show (entryStore vy vs rId).isSome = true; rw [entryStore_r]; rfl
    · show (entryStore vy vs xId).isSome = true; rw [entryStore_x]; rfl
  defsUndefined := fun k hk => by
    rw [show HasVarsImp.definedVars (P := Core.Expression) (copyCfg n T) false = [] from rfl]
      at hk
    cases hk
  definedVarsNotReserved := fun k hk => by
    rw [show HasVarsImp.definedVars (P := Core.Expression) (copyCfg n T) false = [] from rfl]
      at hk
    cases hk
  reservedFresh := by intro _ _ _ _ p hp; simp [testParams] at hp
  factoryDeclared := fun _ _ => rfl
  runtimeFactoryDeclared := fun _ _ => rfl
  initTypesInhabited := fun ty hty => by
    rw [show Imperative.DetCFG.initTypes (copyCfg n T) = [] from rfl] at hty
    cases hty

/-- From the callee entry `entryStore vy vs`, for values `vy` and `vs` of type `T`, the CFG
    body of `copyCfgProc n T` runs to its end. -/
private theorem copyCfg_finishes {n : String} {T : Lambda.LMonoTy}
    {fac : Core.Expression.Factory} {vy vs : Core.Expression.Val}
    (hvy : HasVal.value fac vy) (hvs : HasVal.value fac vs)
    (hty : Core.Logic.Hoare.Procedure.valueHasType T vy)
    (hts : Core.Logic.Hoare.Procedure.valueHasType T vs) :
    ∃ σEnd evs,
      Core.CoreBodyExecE π (copyCfgProc n T).body ⟨entryStore vy vs, fac⟩ σEnd evs := by
  have hset : Core.EvalCommandE π fac (entryStore vy vs) (cfgSet n T)
      (SemanticStore.update (entryStore vy vs) rId vy) [] :=
    .cmd_sem (.eval_set
      ((Core.eval_fvar_of_wellFormedStore (entryStore_wf hvy hvs)).trans (entryStore_x vy vs))
      (UpdateState.of_update (entryStore_r vy vs))
      ⟨vs, .forAll [] T, entryStore_r vy vs,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvs hts,
        Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hvy hty⟩
      (Core.coreEvaluator_WellFormedSemanticEvalVar _))
  exact ⟨_, _, .cfg (.step _ [] _ [] _ (.fetch (copyCfg_lookup n T))
    (.step _ [] _ [] _ (.step_cmd hset) (.step _ [] _ [] _ .finish (.refl _))))⟩

/-- `Id` sees `Core.Factory`. -/
private theorem factory_id : polyAST.factoryBeforeProcedure "Id" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
/-- `IdInt` sees `Core.Factory`. -/
private theorem factory_idInt : polyAST.factoryBeforeProcedure "IdInt" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
/-- `IdCfg` sees `Core.Factory`. -/
private theorem factory_idCfg : polyAST.factoryBeforeProcedure "IdCfg" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
/-- `Relay` sees `Core.Factory`. -/
private theorem factory_relay : polyAST.factoryBeforeProcedure "Relay" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
/-- `PolyToMono` sees `Core.Factory`. -/
private theorem factory_polyToMono :
    polyAST.factoryBeforeProcedure "PolyToMono" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
/-- `MonoToPoly` sees `Core.Factory`. -/
private theorem factory_monoToPoly :
    polyAST.factoryBeforeProcedure "MonoToPoly" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
/-- `RelayCfg` sees `Core.Factory`. -/
private theorem factory_relayCfg : polyAST.factoryBeforeProcedure "RelayCfg" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)

/-- `Id` sees no axiom. -/
private theorem axioms_id (ρ : Env Core.Expression) :
    Core.Specification.AxiomsBeforeProcedureDecl "Id" polyAST ρ :=
  _root_.Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms (by native_decide) ρ
/-- `IdInt` sees no axiom. -/
private theorem axioms_idInt (ρ : Env Core.Expression) :
    Core.Specification.AxiomsBeforeProcedureDecl "IdInt" polyAST ρ :=
  _root_.Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms (by native_decide) ρ
/-- `IdCfg` sees no axiom. -/
private theorem axioms_idCfg (ρ : Env Core.Expression) :
    Core.Specification.AxiomsBeforeProcedureDecl "IdCfg" polyAST ρ :=
  _root_.Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms (by native_decide) ρ

/-- A call to `Id` at `T` runs a copying callee. -/
private theorem id_copyCallee (T : Lambda.LMonoTy) :
    CopyCallee "Id" (some [.forAll [] T]) (copyProc "Id" T) T where
  callee := id_callee T
  header := rfl
  spec := rfl
  contract := id_meets_contract
  factory := factory_id
  axioms := axioms_id
  run := fun _ _ _ _ hb => copyProc_run hb
  gate := fun _ _ _ hfac hvy hvs hty _ => copyProc_gate hfac hvy hvs hty
  finishes := fun _ _ _ _ hvy hvs hty hts => copyProc_finishes hvy hvs hty hts
  transparent := rfl

/-- A call to `IdInt` runs a copying callee. -/
private theorem idInt_copyCallee : CopyCallee "IdInt" (some []) (copyProc "IdInt" .int) .int where
  callee := idInt_callee
  header := rfl
  spec := rfl
  contract := idInt_meets_contract
  factory := factory_idInt
  axioms := axioms_idInt
  run := fun _ _ _ _ hb => copyProc_run hb
  gate := fun _ _ _ hfac hvy hvs hty _ => copyProc_gate hfac hvy hvs hty
  finishes := fun _ _ _ _ hvy hvs hty hts => copyProc_finishes hvy hvs hty hts
  transparent := rfl

/-- A call to `IdCfg` at `T` runs a copying callee with a CFG body. -/
private theorem idCfg_copyCallee (T : Lambda.LMonoTy) :
    CopyCallee "IdCfg" (some [.forAll [] T]) (copyCfgProc "IdCfg" T) T where
  callee := idCfg_callee T
  header := rfl
  spec := rfl
  contract := idCfg_meets_contract
  factory := factory_idCfg
  axioms := axioms_idCfg
  run := fun _ _ _ _ hb => copyCfg_run hb
  gate := fun _ _ _ hfac hvy hvs _ _ => copyCfg_gate hfac hvy hvs
  finishes := fun _ _ _ _ hvy hvs hty hts => copyCfg_finishes hvy hvs hty hts
  transparent := rfl

/-! ### The callers -/

/-- `relayProc n extra T callee tyArgs`, for a procedure `n` that sees `Core.Factory`, is a
    caller `(y, out s)` ensuring `s == y`. -/
private theorem relayProc_caller {n : String}
    {extra : List (Core.Expression.Ident × Lambda.LMonoTy)}
    {T : Lambda.LMonoTy} {callee : String} {tyArgs : Option (List Core.Expression.Ty)}
    (hfac : polyAST.factoryBeforeProcedure n = Core.Factory) :
    RelayCaller n (relayProc n extra T callee tyArgs) T where
  factory := hfac
  input := by simp [relayProc, ListMap.toList]
  output := by simp [relayProc, ListMap.toList]
  post := by simp [relayProc, ListMap.toList]

/-- The clauses of `relayProc n extra T callee tyArgs` type-check. -/
private theorem relayProc_checks (n : String)
    (extra : List (Core.Expression.Ident × Lambda.LMonoTy))
    (T : Lambda.LMonoTy) (callee : String) (tyArgs : Option (List Core.Expression.Ty)) :
    Core.Logic.Hoare.Procedure.contractChecksTyped (relayProc n extra T callee tyArgs) := by
  simp [Core.Logic.Hoare.Procedure.contractChecksTyped, relayProc, ListMap.toList,
    Lambda.LExpr.typeCheck, guard]

/-- **The body of a caller `relayProc n extra T cn tyArgs` meets its contract** when its call
    runs a copying callee: the call ends with `s == y`. -/
private theorem relayProc_triple {n : String}
    {extra : List (Core.Expression.Ident × Lambda.LMonoTy)}
    {T : Lambda.LMonoTy} {cn : String} {tyArgs : Option (List Core.Expression.Ty)}
    {c : Core.Procedure} (hc : CopyCallee cn tyArgs c T)
    (hfac : polyAST.factoryBeforeProcedure n = Core.Factory) :
    Core.Logic.Hoare.Triple π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre (polyAST.factoryBeforeProcedure n)
          (relayProc n extra T cn tyArgs) ρ ∧
        Core.Specification.AxiomsBeforeProcedureDecl n polyAST ρ)
      [Stmt.block "" [Core.Statement.call cn tyArgs (relayArgs T) (cmdMdOf n)] #[]]
      (Core.Logic.Hoare.Procedure.contractPost (polyAST.factoryBeforeProcedure n)
        (relayProc n extra T cn tyArgs))
      (factory := polyAST.factoryBeforeProcedure n) :=
  Core.Logic.Hoare.block π testParams
    (Core.Logic.Hoare.of_storeWF_pre π testParams (relay_call hc (relayProc_caller hfac) _))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ rfl)

/-- **The body of a caller `relayProc n extra T cn tyArgs` meets its contract under total
    correctness** when its call runs a copying callee: the call terminates with `s == y`. -/
private theorem relayProc_triple_total {n : String}
    {extra : List (Core.Expression.Ident × Lambda.LMonoTy)} {T : Lambda.LMonoTy} {cn : String}
    {tyArgs : Option (List Core.Expression.Ty)} {c : Core.Procedure}
    (hc : CopyCallee cn tyArgs c T) (hfac : polyAST.factoryBeforeProcedure n = Core.Factory) :
    Core.Logic.HoareTotal.Triple π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre (polyAST.factoryBeforeProcedure n)
          (relayProc n extra T cn tyArgs) ρ ∧
        Core.Specification.AxiomsBeforeProcedureDecl n polyAST ρ)
      [Stmt.block "" [Core.Statement.call cn tyArgs (relayArgs T) (cmdMdOf n)] #[]]
      (Core.Logic.Hoare.Procedure.contractPost (polyAST.factoryBeforeProcedure n)
        (relayProc n extra T cn tyArgs))
      (factory := polyAST.factoryBeforeProcedure n) :=
  Core.Logic.HoareTotal.block π testParams
    (Core.Logic.HoareTotal.of_storeWF_pre π testParams
      (relay_call_total hc (relayProc_caller hfac) _))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ rfl)

/-- **`Relay` meets its contract**: at every type `T`, its call to `Id` at `T` ends with
    `s == y`. -/
theorem relay_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "Relay" :=
  ⟨_, relay_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl relay_subst
    fun T => ⟨relayProc_checks _ _ _ _ _, relayProc_triple (id_copyCallee T) factory_relay⟩⟩

/-- **`Relay` meets its contract under total correctness**: at every type `T`, its call to
    `Id` at `T` terminates with `s == y`. -/
theorem relay_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "Relay" :=
  ⟨_, relay_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl relay_subst
    fun T => ⟨relayProc_checks _ _ _ _ _, relayProc_triple_total (id_copyCallee T) factory_relay⟩⟩

/-- **The polymorphic `PolyToMono` meets its contract**: at every type, its call to the
    monomorphic `IdInt` ends with `s == y`. -/
theorem polyToMono_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "PolyToMono" :=
  ⟨_, polyToMono_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl polyToMono_subst
    fun _ => ⟨relayProc_checks _ _ _ _ _, relayProc_triple idInt_copyCallee factory_polyToMono⟩⟩

/-- **The polymorphic `PolyToMono` meets its contract under total correctness**: at every
    type, its call to the monomorphic `IdInt` terminates with `s == y`. -/
theorem polyToMono_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "PolyToMono" :=
  ⟨_, polyToMono_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl polyToMono_subst
    fun _ => ⟨relayProc_checks _ _ _ _ _,
      relayProc_triple_total idInt_copyCallee factory_polyToMono⟩⟩

/-- **The monomorphic `MonoToPoly` meets its contract**: its call to the polymorphic `Id` at
    `int` ends with `s == y`. -/
theorem monoToPoly_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "MonoToPoly" :=
  ⟨_, monoToPoly_find, Core.Procedure.forall_instance_of_typeArgs_nil rfl
    ⟨relayProc_checks _ _ _ _ _, relayProc_triple (id_copyCallee .int) factory_monoToPoly⟩⟩

/-- **The monomorphic `MonoToPoly` meets its contract under total correctness**: its call to
    the polymorphic `Id` at `int` terminates with `s == y`. -/
theorem monoToPoly_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "MonoToPoly" :=
  ⟨_, monoToPoly_find, Core.Procedure.forall_instance_of_typeArgs_nil rfl
    ⟨relayProc_checks _ _ _ _ _,
      relayProc_triple_total (id_copyCallee .int) factory_monoToPoly⟩⟩

/-- **`RelayCfg` meets its contract**: at every type `T`, its call to the CFG procedure `IdCfg`
    at `T` ends with `s == y`. -/
theorem relayCfg_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "RelayCfg" :=
  ⟨_, relayCfg_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl relayCfg_subst
    fun T => ⟨relayProc_checks _ _ _ _ _, relayProc_triple (idCfg_copyCallee T) factory_relayCfg⟩⟩

/-- **`RelayCfg` meets its contract under total correctness**: at every type `T`, its call to
    the CFG procedure `IdCfg` at `T` terminates with `s == y`. -/
theorem relayCfg_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "RelayCfg" :=
  ⟨_, relayCfg_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl relayCfg_subst
    fun T => ⟨relayProc_checks _ _ _ _ _,
      relayProc_triple_total (idCfg_copyCallee T) factory_relayCfg⟩⟩

/-! ## A polymorphic function: `CallFirst`

`CallFirst<a>` assigns `first(x, y)` to `r` and ensures `r == first(x, y)`.  It sees the
function `first`, so its factory is not `Core.Factory`, but the proofs read nothing of `first`:
a call to it evaluates to a value of its result type (`Core.eval_app2_op_of_sort`), and to the
same one in every store agreeing on `x` and `y` (`coreEvaluator_WellFormedSemanticEvalExprCongr`),
which `r := first(x, y)` leaves unchanged. -/

/-- The clauses of `callFirstProc T` type-check. -/
private theorem callFirstProc_checks (T : Lambda.LMonoTy) :
    Core.Logic.Hoare.Procedure.contractChecksTyped (callFirstProc T) := by
  simp [Core.Logic.Hoare.Procedure.contractChecksTyped, callFirstProc, ListMap.toList,
    Lambda.LExpr.typeCheck, guard, Lambda.LMonoTy.arrow, Lambda.LMonoTy.isArrow]

/-- `r := first(x, y)`, from an entry with a well-formed store pinned to a factory over `F`,
    ends in `CallFirst`'s postcondition `r == first(x, y)`. -/
private theorem callFirst_post_of_set {F : Lambda.Factory Core.CoreLParams} {T : Lambda.LMonoTy}
    {ρ₀ : Env Core.Expression} {σ' : Core.CoreStore} {w : Core.Expression.Val}
    (hpin : ρ₀.factory.factory = F) (hwf : WellFormedStore ρ₀.store ρ₀.factory)
    (hev : Core.Expression.eval ρ₀.factory ρ₀.store (firstE T) = some w)
    (hup : UpdateState Core.Expression ρ₀.store rId w σ') :
    Core.Logic.Hoare.Procedure.contractPost F (callFirstProc T) { ρ₀ with store := σ' } := by
  have hw : HasVal.value ρ₀.factory w :=
    (Core.coreEvaluator_WellFormedSemanticEvalVal _).outputsAreValues _ _ _ hwf hev
  cases hup with
  | update _ hnew hother =>
    have hwf' : WellFormedStore σ' ρ₀.factory := by
      intro k v hk
      by_cases h : rId = k
      · subst h; rw [hnew] at hk; cases hk; exact hw
      · rw [hother k h] at hk; exact hwf k v hk
    -- `r := first(x, y)` leaves `x` and `y`, and so the value of `first(x, y)`, unchanged.
    have hev' : Core.Expression.eval ρ₀.factory σ' (firstE T) = some w := by
      rw [← hev]
      refine (Core.coreEvaluator_WellFormedSemanticEvalExprCongr _ _ _ _ hwf' hwf
        fun k hk => hother k ?_)
      have hvars : HasFvars.getFvars (P := Core.Expression) (firstE T) = [xId, yId] := rfl
      rw [hvars] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> decide
    intro label check hmem _ _
    simp only [callFirstProc, ListMap.toList, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    refine .inl ⟨hpin, ?_⟩
    change Core.Expression.eval ρ₀.factory σ' (.eq Core.valueLoc (tv rId T) (firstE T)) =
      some (HasBool.ttVal ρ₀.factory)
    exact Core.eval_eq_true _ (Core.eval_fvar _ hnew hw) hev'

/-- **`CallFirst` meets its contract**: at every type, `r := first(x, y)` ends with
    `r == first(x, y)`. -/
theorem callFirst_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple polyAST testParams "CallFirst" :=
  ⟨_, callFirst_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl callFirst_subst
    fun T => by
    refine ⟨callFirstProc_checks T, ?_⟩
    refine Core.Logic.Hoare.block π testParams ?_
      (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ rfl)
    refine Core.Logic.Hoare.of_storeWF_pre π testParams ?_
    exact Core.Logic.Hoare.set π testParams rId _ _ _ _
      fun ρ₀ σ' w ⟨⟨hpre, _⟩, hwf⟩ hev hup => callFirst_post_of_set hpre.2.1 hwf hev hup⟩

/-- **`CallFirst` meets its contract under total correctness**: at every type,
    `r := first(x, y)` terminates and ends with `r == first(x, y)`.  It can execute since
    `first(x, y)` evaluates to a value of the type of `x`, which is the type of the value `r`
    holds. -/
theorem callFirst_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal polyAST testParams "CallFirst" :=
  ⟨_, callFirst_find, Core.Procedure.forall_instance_of_typeArgs_singleton rfl callFirst_subst
    fun T => by
    refine ⟨callFirstProc_checks T, ?_⟩
    refine Core.Logic.HoareTotal.block π testParams ?_
      (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ rfl)
    refine Core.Logic.HoareTotal.of_storeWF_pre π testParams ?_
    refine Core.Logic.HoareTotal.set π testParams rId _ _ _ _
      (fun ρ₀ ⟨⟨hpre, _⟩, hwf⟩ _ => ?_)
      fun ρ₀ σ' w ⟨⟨hpre, _⟩, hwf⟩ hev hup => callFirst_post_of_set hpre.2.1 hwf hev hup
    obtain ⟨vx, hx, htx⟩ := hpre.2.2.2.1 xId T (by simp [callFirstProc, ListMap.toList])
    obtain ⟨vy, hy, hty⟩ := hpre.2.2.2.1 yId T (by simp [callFirstProc, ListMap.toList])
    obtain ⟨vr, hr, htr⟩ := hpre.2.2.2.2 rId T (by simp [callFirstProc, ListMap.toList])
    have hs : vy.sort = vx.sort := Lambda.LSort.toMonoTy_injective (hty.trans htx.symm)
    subst htx
    obtain ⟨w, hev, hwtc, hws⟩ := Core.eval_app2_op_of_sort (m := Core.valueLoc)
      (m' := Core.valueLoc) (m'' := Core.valueLoc) "first"
      ((Core.eval_fvar_of_wellFormedStore (m := Core.valueLoc) (ty := some vx.sort.toMonoTy)
        hwf).trans hx)
      ((Core.eval_fvar_of_wellFormedStore (m := Core.valueLoc) (ty := some vx.sort.toMonoTy)
        hwf).trans hy)
      (hwf _ _ hx) (hwf _ _ hy) rfl hs
    exact ⟨w, hev, vr, .forAll [] vx.sort.toMonoTy, hr,
      Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType (hwf _ _ hr) htr,
      Core.Logic.Hoare.Procedure.valueOfTy_of_valueHasType hwtc (by
        show w.sort.toMonoTy = _; rw [hws])⟩⟩

end Strata.HoarePolymorphicProcedureTest
