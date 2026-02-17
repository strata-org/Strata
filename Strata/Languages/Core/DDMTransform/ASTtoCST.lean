/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Program
import Strata.DDM.Util.DecimalRat

/-!
# Core.Program → CoreCST Conversion

This module converts Core.Program AST to Core CST (concrete syntax).
Used for formatting and pretty-printing Core constructs using DDM's
formatting system.

Known issues:

- Unsupported constructs (coming soon):
  -- Sub-functions (functions defined inside procedures)

- We generate some bound variables' names during translation because the
  semantic AST currently does not preserve them (e.g., bvars in quantifiers).
  We can log the identifier names during CST -> AST translation in the latter's
  metadata field and recover them in the future.

- Misc. formatting issues
  -- Remove extra parentheses around constructors in datatypes, assignments,
  etc.
  -- Remove extra indentation from the last brace of a block or the `end`
  keyword of a mutual block.
-/

namespace Strata

open Core
open Strata.CoreDDM

---------------------------------------------------------------------
-- Conversion Errors
---------------------------------------------------------------------

/-- Errors that can occur during AST→CST conversion -/
inductive ASTToCSTError (M : Type) where
  | unsupportedConstruct (fn : String) (description : String)
                         (context : String) (metadata : M) :
      ASTToCSTError M
  deriving Repr, Inhabited

namespace ASTToCSTError

def toString {M} [ToString M] : ASTToCSTError M → String
  | unsupportedConstruct fn desc ctx _m =>
    s!"Unsupported construct in {fn}: {desc}\nContext: {ctx}"

instance {M} [ToString M] : ToString (ASTToCSTError M) where
  toString := ASTToCSTError.toString

end ASTToCSTError

---------------------------------------------------------------------
-- Core.Program → CoreCST Conversion
---------------------------------------------------------------------

section ToCST

/-- Constants for consistent naming -/
def unknownTypeVar : String := "$__unknown_type"

/-- Generate parameter names efficiently -/
def mkParamName (i : Nat) : String := "a" ++ toString i

/-- Generate quantifier variable names efficiently -/
def mkQuantVarName (level : Nat) : String := "x" ++ toString level

/-- Count the arity of a function type by counting arrows -/
def countArity (ty : TypeExpr) : Nat :=
  match ty with
  | .arrow _ _ rest => 1 + countArity rest
  | _ => 0

structure Scope where
  /-- Track bound variables in this scope -/
  boundVars : Array String := #[]
  deriving Inhabited, Repr

structure ToCSTContext where
  /-- Stack of scopes, with global scope at index 0 -/
  scopes : Array Scope := #[{}]
  /-- Free variables added during conversion -/
  freeVars : Array String := #[]
  deriving Inhabited, Repr

namespace ToCSTContext

def empty : ToCSTContext := { scopes := #[{}] }

/-- Format context for error messages -/
def toErrorString (ctx : ToCSTContext) : String :=
  let lines := ctx.scopes.toList.mapIdx fun i scope =>
    let header := if i = 0 then "Global scope:" else "Scope " ++ toString i ++ ":"
    let bv := if scope.boundVars.isEmpty then ""
              else "\n  boundVars: " ++ toString scope.boundVars.toList
    header ++ bv
  String.intercalate "\n" lines

/-- Get all bound variables across all scopes -/
def boundVars (ctx : ToCSTContext) : Array String :=
  ctx.scopes.foldl (fun acc s => acc ++ s.boundVars) #[]

/-- Find index of bound variable in context -/
def findBoundVarIndex? (ctx : ToCSTContext) (name : String) : Option Nat :=
  ctx.boundVars.findIdx? (· == name)

/-- Find index of free variable in freeVars -/
def freeVarIndex? (ctx : ToCSTContext) (name : String) : Option Nat :=
  ctx.freeVars.findIdx? (· == name)

/-- Add free variables to the context -/
def addFreeVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  { ctx with freeVars := ctx.freeVars ++ names }

/-- Add bound variables to the current scope -/
def addBoundVars (ctx : ToCSTContext) (names : Array String)
    (reverse? : Bool := true) : ToCSTContext :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let names := if reverse? then names.reverse else names
  let newScope := { scope with boundVars := names ++ scope.boundVars }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Push bound variables to the current scope.
Unlike `addBoundVars`, the variable is added to the end of the bound variables.
-/
def pushBoundVar (ctx : ToCSTContext) (name : String)
    : ToCSTContext :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let newScope := { scope with boundVars := scope.boundVars.push name }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Push a new scope onto the stack -/
def pushScope (ctx : ToCSTContext) : ToCSTContext :=
  { ctx with scopes := ctx.scopes.push {} }

/-- Pop the current scope from the stack (never pops scope 0) -/
def popScope (ctx : ToCSTContext) : ToCSTContext :=
  if ctx.scopes.size > 1 then
    { ctx with scopes := ctx.scopes.pop }
  else
    ctx

end ToCSTContext

/-- Monad for AST->CST conversion with context and error tracking -/
abbrev ToCSTM (M : Type) :=
    StateT ToCSTContext (Except (List (ASTToCSTError M)))
/-- Throw an error in ToCSTM -/
def ToCSTM.throwError [Inhabited M] (fn : String)
    (desc : String) (detail : String) : ToCSTM M α := do
  let ctx ← get
  let msg := desc ++ ": " ++ detail
  throw [.unsupportedConstruct fn msg ctx.toErrorString default]

/-- Convert `LMonoTy` to `CoreType` -/
def lmonoTyToCoreType {M} [Inhabited M] (ty : Lambda.LMonoTy) :
    ToCSTM M (CoreType M) := do
  match ty with
  | .ftvar name => pure (.tvar default name)
  | .bitvec 1 => pure (.bv1 default)
  | .bitvec 8 => pure (.bv8 default)
  | .bitvec 16 => pure (.bv16 default)
  | .bitvec 32 => pure (.bv32 default)
  | .bitvec 64 => pure (.bv64 default)
  | .bool => pure (.bool default)
  | .int => pure (.int default)
  | .string => pure (.string default)
  | .real => pure (.real default)
  | .tcons "regex" [] => pure (.regex default)
  | .tcons "Map" [k, v] => do
    let kty ← lmonoTyToCoreType k
    let vty ← lmonoTyToCoreType v
    pure (.Map default kty vty)
  | .tcons "arrow" [a, b] => do
    let aty ← lmonoTyToCoreType a
    let bty ← lmonoTyToCoreType b
    pure (.arrow default aty bty)
  | .tcons name args =>
    let ctx ← get
    match ctx.freeVarIndex? name with
    | some idx => do
      let argTys ← args.mapM lmonoTyToCoreType
      pure (.fvar default idx argTys.toArray)
    | _ => ToCSTM.throwError "lmonoTyToCoreType" "unknown type" (toString ty)
  | _ => ToCSTM.throwError "lmonoTyToCoreType" "unknown type" (toString ty)

/-- Convert `LTy` to `CoreType` -/
def lTyToCoreType {M} [Inhabited M] (ty : Lambda.LTy) : ToCSTM M (CoreType M) :=
  match ty with
  | .forAll _typeVars monoTy => do
    let result ← lmonoTyToCoreType monoTy
    pure result

/-- Convert a type constructor declaration to CST -/
def typeConToCST {M} [Inhabited M] (tcons : TypeConstructor)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let name : Ann String M := ⟨default, tcons.name⟩
  modify (·.addFreeVars #[name.val])
  let args : Ann (Option (Bindings M)) M :=
    if tcons.numargs = 0 then
      ⟨default, none⟩
    else
      let bindings := List.range tcons.numargs |>.map fun i =>
        let paramName : Ann String M := ⟨default, mkParamName i⟩
        let paramType := TypeP.type default
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  pure (.command_typedecl default name args)

/-- Convert a datatype declaration to CST -/
def datatypeToCST {M} [Inhabited M] (datatypes : List (Lambda.LDatatype Visibility))
    (_md : Imperative.MetaData Expression) : ToCSTM M (List (Command M)) := do
  -- Register datatype names first, then constructor/tester/destructor names.
  -- For mutual datatypes, names may already be in context from forward
  -- declarations.
  let dtNames := datatypes.map (·.name)
  for dtName in dtNames.reverse do
    let ctx ← get
    if ctx.freeVarIndex? dtName |>.isNone then
      modify (·.addFreeVars #[dtName])

  -- Then register constructor, tester, and destructor names
  -- for each datatype.
  for dt in datatypes do
    let constrNames := dt.constrs.map (·.name.name)
    let testerNames := dt.constrs.map (·.testerName)
    let destructorNames :=
        dt.constrs.flatMap (fun c => c.args.map
                              (fun (id, _) =>
                                Lambda.destructorFuncName dt id))
    modify (·.addFreeVars (constrNames.toArray ++
                           testerNames.toArray ++
                           destructorNames.toArray))

  let processDatatype (dt : Lambda.LDatatype Visibility) :
      ToCSTM M (Command M) := do
    let name : Ann String M := ⟨default, dt.name⟩
    let args : Ann (Option (Bindings M)) M :=
      if dt.typeArgs.isEmpty then
        ⟨default, none⟩
      else
        let bindings := dt.typeArgs.map fun param =>
          let paramName : Ann String M := ⟨default, param⟩
          let paramType := TypeP.type default
          Binding.mkBinding default paramName paramType
        ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
    let processConstr (c : Lambda.LConstr Visibility) :
          ToCSTM M (Constructor M) := do
      let constrName : Ann String M := ⟨default, c.name.name⟩
      let constrArgs ←
        if c.args.isEmpty then
          pure ⟨default, none⟩
        else do
          let bindings ← c.args.mapM fun (id, ty) => do
            let paramName : Ann String M := ⟨default, id.name⟩
            let paramType ← lmonoTyToCoreType ty
            pure (Binding.mkBinding default paramName (TypeP.expr paramType))
          pure ⟨default, some ⟨default, bindings.toArray⟩⟩
      pure (Constructor.constructor_mk default constrName constrArgs)
    let constrs ← dt.constrs.mapM processConstr
    let constrList ←
      if constrs.isEmpty then
        ToCSTM.throwError "datatypeToCST" "datatype has no constructors" dt.name
      else if constrs.length == 1 then
        pure (ConstructorList.constructorListAtom default constrs[0]!)
      else
        pure (constrs.tail.foldl
          (fun acc c => ConstructorList.constructorListPush default acc c)
          (ConstructorList.constructorListAtom default constrs[0]!))
    pure (.command_datatype default name args constrList)

  match datatypes with
  | [dt] => do
    -- Single datatype - no mutual block needed
    let cmd ← processDatatype dt
    pure [cmd]
  | _ => do
    -- Multiple datatypes - generate forward declarations and mutual block.
    let mut forwardDecls : List (Command M) := []
    for dt in datatypes.reverse do
      let name : Ann String M := ⟨default, dt.name⟩
      let args : Ann (Option (Bindings M)) M :=
        if dt.typeArgs.isEmpty then
          ⟨default, none⟩
        else
          let bindings := dt.typeArgs.map fun param =>
            let paramName : Ann String M := ⟨default, param⟩
            let paramType := TypeP.type default
            Binding.mkBinding default paramName paramType
          ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
      forwardDecls := forwardDecls ++ [.command_forward_typedecl default name args]
    let cmds ← datatypes.mapM processDatatype
    let mutualCmd := Command.command_mutual default ⟨default, cmds.toArray⟩
    pure (forwardDecls ++ [mutualCmd])

/-- Convert a type synonym declaration to CST -/
def typeSynToCST {M} [Inhabited M] (syn : TypeSynonym)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, syn.name⟩
  modify (·.addFreeVars #[name.val])
  let args : Ann (Option (Bindings M)) M :=
    if syn.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let bindings := syn.typeArgs.map fun param =>
        let paramName : Ann String M := ⟨default, param⟩
        let paramType := TypeP.type default
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  let targs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  let rhs ← lmonoTyToCoreType syn.type
  modify ToCSTContext.popScope
  pure (.command_typesynonym default name args targs rhs)

def lconstToExpr {M} [Inhabited M] (c : Lambda.LConst) :
    ToCSTM M (CoreDDM.Expr M) :=
  match c with
  | .boolConst true => pure (.btrue default)
  | .boolConst false => pure (.bfalse default)
  | .intConst n => pure (.natToInt default ⟨default, n.toNat⟩)
  | .realConst r =>
    match Strata.Decimal.fromRat r with
    | some d => pure (.realLit default ⟨default, d⟩)
    | none => ToCSTM.throwError "lconstToExpr" "unsupported real" (toString r)
  | .strConst s => pure (.strLit default ⟨default, s⟩)
  | .bitvecConst 1 n => pure (.bv1Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 8 n => pure (.bv8Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 16 n => pure (.bv16Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 32 n => pure (.bv32Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 64 n => pure (.bv64Lit default ⟨default, n.toNat⟩)
  | .bitvecConst w _ => ToCSTM.throwError "lconstToExpr"
                          "unsupported bitvec width" (toString w)

/-- Handle 0-ary operations -/
def handleZeroaryOps {M} [Inhabited M] (name : String)
    : ToCSTM M (CoreDDM.Expr M) :=
  match name with
  | "Re.All" => pure (.re_all default)
  | "Re.AllChar" => pure (.re_allchar default)
  | "Re.None" => pure (.re_none default)
  | _ => ToCSTM.throwError "lopToExpr" "0-ary op not found" name

/-- Handle unary operations -/
def handleUnaryOps {M} [Inhabited M] (name : String) (arg : CoreDDM.Expr M)
    : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  match name with
  | "old" => pure (.old default ty arg)
  -- Integers and reals
  | "Int.Neg" | "Real.Neg" => pure (.neg_expr default ty arg)
  -- Booleans
  | "Bool.Not" => pure (.not default arg)
  -- Strings and regexes
  | "Str.Length" => pure (.str_len default arg)
  | "Str.ToRegeEx" => pure (.str_toregex default arg)
  | "Re.Star" => pure (.re_star default arg)
  | "Re.Plus" => pure (.re_plus default arg)
  | "Re.Comp" => pure (.re_comp default arg)
  -- Bitvectors
  | "Bv1.Not" => pure (.bvnot default (.bv1 default) arg)
  | "Bv1.Neg" => pure (.neg_expr default (.bv1 default) arg)
  | "Bv8.Not" => pure (.bvnot default (.bv8 default) arg)
  | "Bv8.Neg" => pure (.neg_expr default (.bv8 default) arg)
  | "Bv16.Not" => pure (.bvnot default (.bv16 default) arg)
  | "Bv16.Neg" => pure (.neg_expr default (.bv16 default) arg)
  | "Bv32.Not" => pure (.bvnot default (.bv32 default) arg)
  | "Bv32.Neg" => pure (.neg_expr default (.bv32 default) arg)
  | "Bv64.Not" => pure (.bvnot default (.bv64 default) arg)
  | "Bv64.Neg" => pure (.neg_expr default (.bv64 default) arg)
  | "Bv8.Extract_7_7" => pure (.bvextract_7_7 default arg)
  | "Bv16.Extract_15_15" => pure (.bvextract_15_15 default arg)
  | "Bv32.Extract_31_31" => pure (.bvextract_31_31 default arg)
  | "Bv16.Extract_7_0" => pure (.bvextract_7_0_16 default arg)
  | "Bv32.Extract_7_0" => pure (.bvextract_7_0_32 default arg)
  | "Bv32.Extract_15_0" => pure (.bvextract_15_0_32 default arg)
  | "Bv64.Extract_7_0" => pure (.bvextract_7_0_64 default arg)
  | "Bv64.Extract_15_0" => pure (.bvextract_15_0_64 default arg)
  | "Bv64.Extract_31_0" => pure (.bvextract_31_0_64 default arg)
  | _ => ToCSTM.throwError "handleUnaryOps" "unary op" name

/-- Map from bitvector binary operation base names to DDM Expr constructors -/
def bvBinaryOpMap {M} [Inhabited M] :
    List (String × (CoreType M → CoreDDM.Expr M → CoreDDM.Expr M → CoreDDM.Expr M)) :=
 [
  ("And", fun ty arg1 arg2 => .bvand default ty arg1 arg2),
  ("Or", fun ty arg1 arg2 => .bvor default ty arg1 arg2),
  ("Xor", fun ty arg1 arg2 => .bvxor default ty arg1 arg2),
  ("Add", fun ty arg1 arg2 => .add_expr default ty arg1 arg2),
  ("Sub", fun ty arg1 arg2 => .sub_expr default ty arg1 arg2),
  ("Mul", fun ty arg1 arg2 => .mul_expr default ty arg1 arg2),
  ("UDiv", fun ty arg1 arg2 => .div_expr default ty arg1 arg2),
  ("UMod", fun ty arg1 arg2 => .mod_expr default ty arg1 arg2),
  ("SDiv", fun ty arg1 arg2 => .bvsdiv default ty arg1 arg2),
  ("SMod", fun ty arg1 arg2 => .bvsmod default ty arg1 arg2),
  ("Shl", fun ty arg1 arg2 => .bvshl default ty arg1 arg2),
  ("UShr", fun ty arg1 arg2 => .bvushr default ty arg1 arg2),
  ("SShr", fun ty arg1 arg2 => .bvsshr default ty arg1 arg2),
  ("ULe", fun ty arg1 arg2 => .le default ty arg1 arg2),
  ("ULt", fun ty arg1 arg2 => .lt default ty arg1 arg2),
  ("UGe", fun ty arg1 arg2 => .ge default ty arg1 arg2),
  ("UGt", fun ty arg1 arg2 => .gt default ty arg1 arg2),
  ("SLe", fun ty arg1 arg2 => .bvsle default ty arg1 arg2),
  ("SLt", fun ty arg1 arg2 => .bvslt default ty arg1 arg2),
  ("SGe", fun ty arg1 arg2 => .bvsge default ty arg1 arg2),
  ("SGt", fun ty arg1 arg2 => .bvsgt default ty arg1 arg2)
]

/-- Map from bitvector sizes to their corresponding type constructors -/
def bvTypeMap {M} [Inhabited M] : List (Nat × (CoreType M)) := [
  (1, .bv1 default),
  (8, .bv8 default),
  (16, .bv16 default),
  (32, .bv32 default),
  (64, .bv64 default)
]

/-- Map from bitvector sizes to their corresponding concat operations -/
def bvConcatMap {M} [Inhabited M] :
    List (Nat × (CoreDDM.Expr M → CoreDDM.Expr M → CoreDDM.Expr M)) := [
  (8, fun arg1 arg2 => .bvconcat8 default arg1 arg2),
  (16, fun arg1 arg2 => .bvconcat16 default arg1 arg2),
  (32, fun arg1 arg2 => .bvconcat32 default arg1 arg2)
]

/-- Auto-generated bitvector binary operations handler -/
def handleBitvecBinaryOps {M} [Inhabited M] (name : String) (arg1 arg2 : CoreDDM.Expr M)
    : ToCSTM M (CoreDDM.Expr M) :=
  -- Parse operation name: "BvN.Op" -> (N, "Op")
  let parts := name.splitOn "."
  match parts with
  | [sizeStr, opName] =>
    if sizeStr.startsWith "Bv" then
      let sizeNumStr := sizeStr.drop 2
      match sizeNumStr.toNat? with
      | some size =>
        -- Look up type for this size
        match (bvTypeMap).find? (·.1 == size) with
        | some (_, ty) =>
          -- Handle concat operations
          if opName == "Concat" then
            match (bvConcatMap).find? (·.1 == size) with
            | some (_, concatOp) => pure (concatOp arg1 arg2)
            | none => ToCSTM.throwError "handleBitvecBinaryOps"
                          "unsupported concat size" (toString size)
          else
            -- Handle regular binary operations
            match (bvBinaryOpMap).find? (·.1 == opName) with
            | some (_, op) => pure (op ty arg1 arg2)
            | none => ToCSTM.throwError "handleBitvecBinaryOps"
                              "unknown bitvec op" opName
        | none => ToCSTM.throwError "handleBitvecBinaryOps"
                      "unsupported bitvec size" (toString size)
      | none => ToCSTM.throwError "handleBitvecBinaryOps"
                  "invalid size format" (toString sizeNumStr)
    else
      ToCSTM.throwError "handleBitvecBinaryOps"
              "not a bitvec operation" name
  | _ => ToCSTM.throwError "handleBitvecBinaryOps"
          "invalid operation format" name

/-- Handle binary operations -/
def handleBinaryOps {M} [Inhabited M] (name : String)
    (arg1 arg2 : CoreDDM.Expr M) : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  match name with
  -- Integer and Real operations
  | "Int.Add" | "Real.Add" => pure (.add_expr default ty arg1 arg2)
  | "Int.Sub" | "Real.Sub" => pure (.sub_expr default ty arg1 arg2)
  | "Int.Mul" | "Real.Mul" => pure (.mul_expr default ty arg1 arg2)
  | "Int.Div" | "Real.Div" => pure (.div_expr default ty arg1 arg2)
  | "Int.Mod" => pure (.mod_expr default ty arg1 arg2)
  | "Int.Le" | "Real.Le" => pure (.le default ty arg1 arg2)
  | "Int.Lt" | "Real.Lt" => pure (.lt default ty arg1 arg2)
  | "Int.Ge" | "Real.Ge" => pure (.ge default ty arg1 arg2)
  | "Int.Gt" | "Real.Gt" => pure (.gt default ty arg1 arg2)
  -- Boolean operations
  | "Bool.And" => pure (.and default arg1 arg2)
  | "Bool.Or" => pure (.or default arg1 arg2)
  | "Bool.Implies" => pure (.implies default arg1 arg2)
  | "Bool.Equiv" => pure (.equiv default arg1 arg2)
  -- Map operations
  | "select" => pure (.map_get default ty ty arg1 arg2)
  -- String and Regex operations
  | "Str.Concat" => pure (.str_concat default arg1 arg2)
  | "Str.InRegEx" => pure (.str_inregex default arg1 arg2)
  | "Re.Range" => pure (.re_range default arg1 arg2)
  | "Re.Concat" => pure (.re_concat default arg1 arg2)
  | "Re.Union" => pure (.re_union default arg1 arg2)
  | "Re.Inter" => pure (.re_inter default arg1 arg2)
  | _ => handleBitvecBinaryOps name arg1 arg2

/-- Handle ternary operations -/
def handleTernaryOps {M} [Inhabited M] (name : String)
    (arg1 arg2 arg3 : CoreDDM.Expr M) : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  match name with
  -- Maps
  | "update" => pure (.map_set default ty ty arg1 arg2 arg3)
  -- Strings and regexes
  | "Str.Substr" => pure (.str_substr default arg1 arg2 arg3)
  | "Re.Loop" => pure (.re_loop default arg1 arg2 arg3)
  | _ => ToCSTM.throwError "handleTernaryOps" "ternary op not found " name

def lopToExpr {M} [Inhabited M]
    (name : String) (args : List (CoreDDM.Expr M))
    : ToCSTM M (CoreDDM.Expr M) := do
  let ctx ← get
  -- User-defined functions.
  match ctx.freeVarIndex? name with
  | some idx =>
    let fnExpr := CoreDDM.Expr.fvar default idx
    pure <| args.foldl (fun acc arg => .app default acc arg) fnExpr
  | none =>
    -- Either a built-in or an invalid operation.
    match args with
    | [] => handleZeroaryOps name
    | [arg] => handleUnaryOps name arg
    | [arg1, arg2] => handleBinaryOps name arg1 arg2
    | [arg1, arg2, arg3] => handleTernaryOps name arg1 arg2 arg3
    | _ => ToCSTM.throwError "lopToExpr" "unknown operation" name

mutual
/-- Convert `Lambda.LExpr` to Core `Expr` -/
partial def lexprToExpr {M} [Inhabited M]
    (e : Lambda.LExpr CoreLParams.mono) (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let ctx ← get
  match e with
  | .const _ c => lconstToExpr c
  | .bvar _ idx =>
    if idx < ctx.boundVars.size then
      pure (.bvar default idx)
    else
      ToCSTM.throwError "lexprToExpr" "bvar index out of bounds" (toString idx)
  | .fvar _ id _ =>
    -- We first look for Lambda .fvars in the boundVars context, before checking
    -- the freeVars context. Lambda .fvars can come from formals of a function
    -- or procedure (which are .bvars in DDM), but also from global variable
    -- declaration (which are DDM .fvars). Note that Strata Core does not allow
    -- variable shadowing.
    match ctx.findBoundVarIndex? id.name with
    | some idx => pure (.bvar default (ctx.boundVars.size - (idx + 1)))
    | none =>
      match ctx.freeVarIndex? id.name with
      | some idx => pure (.fvar default idx)
      | none => do
        -- Likely this .fvar is generated in an evaluated Core program (i.e.,
        -- after analysis). Add to the context.
        modify (·.addFreeVars #[id.name])
        pure (.fvar default (ctx.freeVars.size))
  | .ite _ c t f => liteToExpr c t f qLevel
  | .eq _ e1 e2 => leqToExpr e1 e2 qLevel
  | .op _ name _ => lopToExpr name.name []
  | .app _ _ _ => lappToExpr e qLevel
  | .abs _ _ _ => ToCSTM.throwError "lexprToExpr"
                    "lambda not supported in CoreDDM" ""
  | .quant _ qkind ty trigger body =>
    lquantToExpr qkind ty trigger body (qLevel + 1)

/-- Extract trigger patterns from Lambda's trigger expression representation -/
partial def extractTriggerPatterns {M} [Inhabited M]
    (trigger : Lambda.LExpr CoreLParams.mono) (qLevel : Nat)
    : ToCSTM M (Array (CoreDDM.Expr M)) := do
  match trigger with
  | .bvar _ 0 => pure #[]  -- noTrigger
  | .app _ (.app _ (.op _ name _) triggerExpr) rest =>
    if name.name == "TriggerGroup.addTrigger" then
      let expr ← lexprToExpr triggerExpr qLevel
      let restExprs ← extractTriggerPatterns rest qLevel
      pure (#[expr] ++ restExprs)
    else if name.name == "Triggers.addGroup" then
      -- Triggers.addGroup adds a trigger group to a triggers list
      -- triggerExpr is a TriggerGroup, rest is the Triggers list
      let groupExprs ← extractTriggerPatterns triggerExpr qLevel
      let restExprs ← extractTriggerPatterns rest qLevel
      pure (groupExprs ++ restExprs)
    else
      ToCSTM.throwError "extractTriggerPatterns"
              "unexpected trigger operation" name.name
  | .op _ name _ =>
    if name.name == "TriggerGroup.empty" ||
       name.name == "Triggers.empty" then
      pure #[]
    else
      ToCSTM.throwError "extractTriggerPatterns"
          "unexpected trigger operation" name.name
  | _ =>
    -- Single trigger expression
    let expr ← lexprToExpr trigger qLevel
    pure #[expr]

partial def lquantToExpr {M} [Inhabited M]
    (qkind : Lambda.QuantifierKind) (ty : Option Lambda.LMonoTy)
    (trigger : Lambda.LExpr CoreLParams.mono) (body : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let name : Ann String M := ⟨default, mkQuantVarName (qLevel - 1)⟩
  modify (·.addBoundVars #[name.val])
  let tyExpr ← match ty with
    | some t => lmonoTyToCoreType t
    | none => pure (CoreType.tvar default unknownTypeVar)
  let bind := Bind.bind_mk default name ⟨default, none⟩ tyExpr
  let dl := DeclList.declAtom default bind
  let hasNoTrigger := trigger matches .bvar _ 0
  if hasNoTrigger then
    let bodyExpr ← lexprToExpr body qLevel
    match qkind with
    | .all => pure (.forall default dl bodyExpr)
    | .exist => pure (.exists default dl bodyExpr)
  else
    let triggerExprs ← extractTriggerPatterns trigger qLevel
    let bodyExpr ← lexprToExpr body qLevel
    let trigAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, triggerExprs.reverse⟩
    let tg := TriggerGroup.trigger default trigAnn
    let tl := Triggers.triggersAtom default tg
    match qkind with
    | .all => pure (.forallT default dl tl bodyExpr)
    | .exist => pure (.existsT default dl tl bodyExpr)

partial def liteToExpr {M} [Inhabited M]
    (c t f : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let cExpr ← lexprToExpr c qLevel
  let tExpr ← lexprToExpr t qLevel
  let fExpr ← lexprToExpr f qLevel
  let ty := CoreType.bool default
  pure (.if default ty cExpr tExpr fExpr)

partial def leqToExpr {M} [Inhabited M]
    (e1 e2 : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat) :
    ToCSTM M (CoreDDM.Expr M) := do
  let e1Expr ← lexprToExpr e1 qLevel
  let e2Expr ← lexprToExpr e2 qLevel
  let ty := CoreType.bool default
  pure (.equal default ty e1Expr e2Expr)

partial def lappToExpr {M} [Inhabited M]
    (e : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat) (acc : List (CoreDDM.Expr M) := [])
    : ToCSTM M (CoreDDM.Expr M) :=
  match e with
  | .app _ (.app m fn e1) e2 => do
    let e2Expr ← lexprToExpr e2 qLevel
    lappToExpr (.app m fn e1) qLevel (e2Expr :: acc)
  | .app _ (.op _ fn _) e1 => do
    let e1Expr ← lexprToExpr e1 qLevel
    lopToExpr fn.name (e1Expr :: acc)
  | _ =>
    ToCSTM.throwError "lappToExpr" "unsupported application" (toString e)
end

/-- Convert a function declaration to a statement -/
def funcDeclToStatement {M} [Inhabited M] (decl : Imperative.PureFunc Expression)
    : ToCSTM M (CoreDDM.Statement M) := do
  let name : Ann String M := ⟨default, decl.name.name⟩
  let typeArgs : Ann (Option (TypeArgs M)) M :=
    if decl.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let tvars := decl.typeArgs.map fun tv =>
        TypeVar.type_var default (⟨default, tv⟩ : Ann String M)
      ⟨default, some (TypeArgs.type_args default ⟨default, tvars.toArray⟩)⟩
  let processInput (id : CoreLParams.Identifier) (ty : Lambda.LTy) :
          ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.name⟩
    let paramType ← lTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.name)
  let results ← decl.inputs.toArray.mapM (fun (id, ty) => processInput id ty)
  let bindings := results.map (·.1)
  let paramNames := results.map (·.2)
  let b : Bindings M := .mkBindings default ⟨default, bindings⟩
  let r ← lTyToCoreType decl.output
  let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
  match decl.body with
  | none =>
    dbg_trace f!"funcDeclToStatement: funcDecl without body not supported in statements"
    -- Dummy expr for the body
    let bodyExpr := .fvar default (←get).freeVars.size
    pure (.funcDecl_statement default name typeArgs b r bodyExpr inline?)
  | some body => do
    -- Add formals to the context
    modify (·.addBoundVars (reverse? := false) paramNames)
    let bodyExpr ← lexprToExpr body 0
    pure (.funcDecl_statement default name typeArgs b r bodyExpr inline?)

mutual
/-- Convert `Core.Statement` to `CoreDDM.Statement` -/
partial def stmtToCST {M} [Inhabited M] (s : Core.Statement)
    : ToCSTM M (CoreDDM.Statement M) := do
  match s with
  | .init name ty expr _md => do
    let nameAnn : Ann String M := ⟨default, name.toPretty⟩
    let tyCST ← lTyToCoreType ty
    let result ← match expr with
    | .fvar _ f _ =>
      let ctx ← get
      match ctx.freeVarIndex? f.name with
      | some idx =>
        let exprCST := CoreDDM.Expr.fvar default idx
        pure (.initStatement default tyCST nameAnn exprCST)
      | none => do
        -- If this free variable isn't in scope, it's autogenerated in
        -- Core (i.e., default/havoc init value).
        let bind := Bind.bind_mk default nameAnn
                    ⟨default, none⟩ tyCST
        let dl := DeclList.declAtom default bind
        pure (.varStatement default dl)
    | _ => -- not an .fvar
      let exprCST ← lexprToExpr expr 0
      pure (.initStatement default tyCST nameAnn exprCST)
    -- Push the newly declared variable to the *end of the bound variables
    -- context* so that the most recently declared variable has the lowest
    -- index.
    modify (·.pushBoundVar name.toPretty)
    pure result
  | .set name expr _md => do
    let lhs := Lhs.lhsIdent default ⟨default, name.name⟩
    let exprCST ← lexprToExpr expr 0
    -- Type annotation required by CST but not semantically used.
    let tyCST := CoreType.tvar default unknownTypeVar
    pure (.assign default tyCST lhs exprCST)
  | .havoc name _md => do
    let nameAnn : Ann String M := ⟨default, name.name⟩
    pure (.havoc_statement default nameAnn)
  | .assert label expr _md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    pure (.assert default labelAnn exprCST)
  | .assume label expr _md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    pure (.assume default labelAnn exprCST)
  | .cover label expr _md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    pure (.cover default labelAnn exprCST)
  | .call lhs pname args _md => do
    let lhsAnn := ⟨default, lhs.toArray.map fun id => ⟨default, id.name⟩⟩
    let pnameAnn : Ann String M := ⟨default, pname⟩
    let argsCST ← args.toArray.mapM (fun a => lexprToExpr a 0)
    let argsAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, argsCST⟩
    pure (.call_statement default lhsAnn pnameAnn argsAnn)
  | .block label stmts _md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    let blockCST ← blockToCST stmts
    pure (.block_statement default labelAnn blockCST)
  | .ite cond thenb elseb _md => do
    let condCST ← lexprToExpr cond 0
    let thenCST ← blockToCST thenb
    let elseCST ← elseToCST elseb
    pure (.if_statement default condCST thenCST elseCST)
  | .loop guard _measure invariant body _md => do
    let guardCST ← lexprToExpr guard 0
    let invs ← invariantsToCST invariant
    let bodyCST ← blockToCST body
    pure (.while_statement default guardCST invs bodyCST)
  | .goto label _md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    pure (.goto_statement default labelAnn)
  | .funcDecl decl _md => funcDeclToStatement decl

partial def blockToCST [Inhabited M] (stmts : List Core.Statement)
    : ToCSTM M (CoreDDM.Block M) := do
  modify ToCSTContext.pushScope
  let stmtsCST ← stmts.toArray.mapM stmtToCST
  modify ToCSTContext.popScope
  pure (.block default ⟨default, stmtsCST⟩)

partial def elseToCST {M} [Inhabited M] (stmts : List Core.Statement)
    : ToCSTM M (Else M) := do
  if stmts.isEmpty then
    pure (.else0 default)
  else
    let blockCST ← blockToCST stmts
    pure (.else1 default blockCST)

partial def invariantsToCST {M} [Inhabited M]
    (inv : Option (Lambda.LExpr CoreLParams.mono)) : ToCSTM M (Invariants M) :=
  match inv with
  | none => pure (.nilInvariants default)
  | some expr => do
    let exprCST ← lexprToExpr expr 0
    pure (.consInvariants default exprCST (.nilInvariants default))
end

/-- Convert a procedure to CST
N.B.: We don't add the procedure name to the freeVars in the context.
-/
def procToCST {M} [Inhabited M] (proc : Core.Procedure) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, proc.header.name.toPretty⟩
  let typeArgs : Ann (Option (TypeArgs M)) M :=
    if proc.header.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let tvars := proc.header.typeArgs.map fun tv =>
        TypeVar.type_var default (⟨default, tv⟩ : Ann String M)
      ⟨default, some (TypeArgs.type_args default ⟨default, tvars.toArray⟩)⟩
  let processInput (id : CoreIdent) (ty : Lambda.LMonoTy) : ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.toPretty⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.toPretty)
  let inputResults ← proc.header.inputs.toArray.mapM (fun (id, ty) => processInput id ty)
  let inputBindings := inputResults.map (·.1)
  let inputNames := inputResults.map (·.2)
  let inputs : Bindings M := .mkBindings default ⟨default, inputBindings⟩
  let processOutput (id : CoreIdent) (ty : Lambda.LMonoTy) : ToCSTM M (MonoBind M × String) := do
    let nameAnn : Ann String M := ⟨default, id.toPretty⟩
    let tyCST ← lmonoTyToCoreType ty
    pure (MonoBind.mono_bind_mk default nameAnn tyCST, id.toPretty)
  let outputResults ← proc.header.outputs.toArray.mapM (fun (id, ty) => processOutput id ty)
  let outputBinds := outputResults.map (·.1)
  let outputNames := outputResults.map (·.2)
  modify (ToCSTContext.addBoundVars (reverse? := false) · outputNames)
  modify (ToCSTContext.addBoundVars (reverse? := false) · inputNames)
  let outputs : Ann (Option (MonoDeclList M)) M :=
    if outputBinds.isEmpty then
      ⟨default, none⟩
    else
      let declList := outputBinds[1:].foldl
        (fun acc bind => MonoDeclList.monoDeclPush default acc bind)
        (MonoDeclList.monoDeclAtom default outputBinds[0]!)
      ⟨default, some declList⟩
  -- Build spec elements
  let mut specElts : Array (SpecElt M) := #[]
  -- Add modifies
  for id in proc.spec.modifies do
    let modSpec := SpecElt.modifies_spec default ⟨default, id.name⟩
    specElts := specElts.push modSpec
  -- Add requires
  let freeAnn : Ann (Option (Free M)) M := ⟨default, none⟩
  for (label, check) in proc.spec.preconditions.toList do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr check.expr 0
    let reqSpec := SpecElt.requires_spec default labelAnn freeAnn exprCST
    specElts := specElts.push reqSpec
  -- Add ensures
  for (label, check) in proc.spec.postconditions.toList do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr check.expr 0
    let ensSpec := SpecElt.ensures_spec default labelAnn freeAnn exprCST
    specElts := specElts.push ensSpec
  let specAnn : Ann (Array (SpecElt M)) M := ⟨default, specElts⟩
  let spec : Ann (Option (Spec M)) M :=
    if specElts.isEmpty then
      ⟨default, none⟩
    else
      ⟨default, some (Spec.spec_mk default specAnn)⟩
  let bodyCST ← blockToCST proc.body
  let body : Ann (Option (CoreDDM.Block M)) M := ⟨default, some bodyCST⟩
  modify ToCSTContext.popScope
  pure (.command_procedure default name typeArgs inputs outputs spec body)

/-- Convert a function declaration to CST -/
def funcToCST {M} [Inhabited M]
    (func : Lambda.LFunc CoreLParams)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, func.name.name⟩
  let typeArgs : Ann (Option (TypeArgs M)) M :=
    if func.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let tvars := func.typeArgs.map fun tv =>
        TypeVar.type_var default (⟨default, tv⟩ : Ann String M)
      ⟨default, some (TypeArgs.type_args default ⟨default, tvars.toArray⟩)⟩
  let processInput (id : CoreLParams.Identifier) (ty : Lambda.LMonoTy) :
          ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.name⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.name)
  let results ← func.inputs.toArray.mapM (fun (id, ty) => processInput id ty)
  let bindings := results.map (·.1)
  let paramNames := results.map (·.2)
  let b : Bindings M := .mkBindings default ⟨default, bindings⟩
  let r ← lmonoTyToCoreType func.output
  let result ← match func.body with
  | none => pure (.command_fndecl default name typeArgs b r)
  | some body => do
    -- Add formals to the context.
    modify (·.addBoundVars (reverse? := false) paramNames)
    let bodyExpr ← lexprToExpr body 0
    let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
    pure (.command_fndef default name typeArgs b r bodyExpr inline?)
  modify ToCSTContext.popScope
  -- Register function name as free variable.
  modify (·.addFreeVars #[name.val])
  pure result

/-- Convert an axiom to CST -/
def axiomToCST {M} [Inhabited M] (ax : Axiom)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨
      default, some (.label default ⟨default, ax.name⟩)⟩
  let exprCST ← lexprToExpr ax.e 0
  pure (.command_axiom default labelAnn exprCST)

/-- Convert a distinct declaration to CST -/
def distinctToCST {M} [Inhabited M] (name : CoreIdent) (es : List (Lambda.LExpr CoreLParams.mono))
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, name.toPretty⟩)⟩
  let exprsCST ← es.mapM (fun a => lexprToExpr a 0)
  let exprsAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, exprsCST.toArray⟩
  pure (.command_distinct default labelAnn exprsAnn)

/-- Convert a variable declaration to CST -/
def varToCST {M} [Inhabited M]
    (name : CoreIdent) (ty : Lambda.LTy) (_e : Lambda.LExpr CoreLParams.mono)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  -- Register name as free variable
  modify (·.addFreeVars #[name.toPretty])
  let nameAnn : Ann String M := ⟨default, name.toPretty⟩
  let tyCST ← lTyToCoreType ty
  let typeArgs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  let bind := Bind.bind_mk default nameAnn typeArgs tyCST
  pure (.command_var default bind)

/-- Convert a `Core.Decl` to a Core `Command` -/
def declToCST {M} [Inhabited M] (decl : Core.Decl) : ToCSTM M (List (Command M)) :=
  match decl with
  | .var name ty e md => do
    let cmd ← varToCST name ty e md
    pure [cmd]
  | .type (.con tcons) md => do
    let cmd ← typeConToCST tcons md
    pure [cmd]
  | .type (.syn syn) md => do
    let cmd ← typeSynToCST syn md
    pure [cmd]
  | .type (.data datatypes) md =>
    datatypeToCST datatypes md
  | .func func md => do
    let cmd ← funcToCST func md
    pure [cmd]
  | .proc proc _md => do
    let cmd ← procToCST proc
    pure [cmd]
  | .ax ax md => do
    let cmd ← axiomToCST ax md
    pure [cmd]
  | .distinct name es md => do
    let cmd ← distinctToCST name es md
    pure [cmd]

/-- Convert `Core.Program` to a list of CST `Commands` -/
def programToCST {M} [Inhabited M] (prog : Core.Program) :
    ToCSTM M (List (Command M)) := do
  let cmdLists ← prog.decls.mapM declToCST
  pure cmdLists.flatten

-- Recreate enough of `GlobalContext` from `ToCSTContext` obtained from
-- `programToCST`, purely for formatting. See `printProgram` below.
private def recreateGlobalContext (ctx : ToCSTContext) : GlobalContext :=
  let (nameMap, _) := ctx.freeVars.foldl
    (init := (Std.HashMap.emptyWithCapacity, 0)) fun (map, i) name =>
    (map.insert name i, i + 1)
  let vars := ctx.freeVars.map fun name =>
    -- .fvar below is really a dummy value.
    (name, GlobalKind.expr (.fvar default 0 #[]), DeclState.defined)
  { nameMap, vars }

/-- Render `Core.Program` to a format object. -/
def Core.formatProgram (ast : Core.Program) : Std.Format :=
  match (programToCST (M := SourceRange) ast).run ToCSTContext.empty with
  | .error errs =>
    Std.format "AST to CST Error:\n" ++
    Std.Format.joinSep (errs.map (Std.format ∘ repr)) "\n"
  | .ok (cmds, finalCtx) =>
    let dialects := CoreDDM.dialectMap
    -- Format with recreated global context
    let ddmCtx := recreateGlobalContext finalCtx
    let ctx := FormatContext.ofDialects dialects ddmCtx {}
    let state : FormatState := {
      openDialects := dialects.toList.foldl (init := {})
        fun a (d : Dialect) => a.insert d.name
    }
    Std.Format.joinSep (cmds.map fun cmd =>
                          (mformat (ArgF.op cmd.toAst) ctx state).format) ""

end ToCST

---------------------------------------------------------------------
end Strata
