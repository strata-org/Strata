/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program

-- We define the AST for our language here.

-- The CST and grammar are defined in `DDMTransform/Parse.lean`
-- Legacy conversion to this AST is in `DDMTransform/TranslateOld.lean`.
-- The current verifier pipeline uses generated `BooleDDM.*` (see `Verify.lean`)
-- and lowers directly to Core, bypassing this legacy frontend AST.
-- Typechecking in the active pipeline is done by `Strata.Boole.typeCheck`
-- in `Verify.lean` via Core typechecking.
-- Verification / symbolic execution and VC generation in the active pipeline
-- is done by `Strata.Boole.verify` in `Verify.lean` via `Core.verify`.

namespace Strata.Boole

open Std Imperative Lambda

inductive Visibility where
  | unres
  | glob
  | locl
  | temp
  deriving DecidableEq, Repr, Inhabited

instance : ToFormat Visibility where
  format
  | .unres => "u:"
  | .glob => "g:"
  | .locl => "l:"
  | .temp => "t:"

abbrev BooleIdent := Lambda.Identifier Visibility

abbrev BooleExprMetadata := Unit
abbrev BooleLParams: Lambda.LExprParams := {Metadata := BooleExprMetadata, IDMeta := Visibility}
abbrev BooleLabel := String

@[match_pattern]
def BooleIdent.unres (s : String) : BooleIdent := ⟨s, Visibility.unres⟩
@[match_pattern]
def BooleIdent.glob (s : String) : BooleIdent := ⟨s, Visibility.glob⟩
@[match_pattern]
def BooleIdent.locl (s : String) : BooleIdent := ⟨s, Visibility.locl⟩
@[match_pattern]
def BooleIdent.temp (s : String) : BooleIdent := ⟨s, Visibility.temp⟩

def BooleIdent.isUnres (id : BooleIdent) : Bool := match id with
  | .unres _ => true | _ => false
def BooleIdent.isGlob (id : BooleIdent) : Bool := match id with
  | .glob _ => true | _ => false
def BooleIdent.isLocl (id : BooleIdent) : Bool := match id with
  | .locl _ => true | _ => false
def BooleIdent.isTemp (id : BooleIdent) : Bool := match id with
  | .temp _ => true | _ => false

def BooleIdent.toPretty (x : BooleIdent) : String :=
  match x with | ⟨s, _⟩ => s

instance : Coe String BooleIdent where
  coe | s => .unres s

instance : Inhabited BooleIdent where
  default := ⟨"_", .unres⟩

def ExpressionMetadata := Unit

instance : DecidableEq ExpressionMetadata :=
  show DecidableEq Unit from inferInstance

instance : Repr ExpressionMetadata :=
  show Repr Unit from inferInstance

abbrev Expression : Imperative.PureExpr :=
   { Ident := BooleIdent,
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, Visibility⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     ExprMetadata := ExpressionMetadata,
     TyEnv := @Lambda.TEnv Visibility,
     TyContext := @Lambda.LContext ⟨ExpressionMetadata, Visibility⟩,
     EvalEnv := Lambda.LState ⟨ExpressionMetadata, Visibility⟩
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier _)) }

inductive Boundedness where
  | Finite
  | Infinite -- Default
  deriving Repr

structure TypeConstructor where
  -- (TODO) Add SMT support for Core's Finite types.
  bound    : Boundedness := .Infinite
  name     : String
  -- Core treats
  -- `type Foo a a;` // or type Foo _ _;
  -- the same as
  -- `type Foo a b;`
  -- That is, the exact identifier is irrelevant. As such, we only
  -- record the number of arguments in a type constructor here.
  numargs  : Nat
  deriving Repr

instance : ToFormat TypeConstructor where
  format t :=
    let args := (List.replicate t.numargs "_").toString
    f!"type {repr t.bound} {t.name} {args}"

def TypeConstructor.toType (t : TypeConstructor) : LTy :=
  let typeargs := List.replicate t.numargs "_ty"
  let ids := typeargs.mapIdx (fun i elem => (elem ++ toString i))
  let args := typeargs.mapIdx (fun i elem => LMonoTy.ftvar (elem ++ toString i))
  .forAll ids (.tcons t.name args)

structure TypeSynonym where
  name     : String
  -- Unlike in `TypeConstructor` above, the arguments are relevant
  -- here. E.g., for a type declared like so:
  -- `type Foo _ _;`
  -- the type synonym
  -- `type Bar x y = Foo x x;`
  -- is legal, where `y` is ignored.
  -- Note also that the `typeArgs` may not contain duplicates.
  typeArgs : List TyIdentifier
  type     : LMonoTy
  deriving Repr

instance : ToFormat TypeSynonym where
  format t :=
    let args := if t.typeArgs.isEmpty then f!"" else f!" {Format.joinSep t.typeArgs " "}"
    f!"type {t.name}{args} := {t.type}"

def TypeSynonym.toLHSLMonoTy (t : TypeSynonym) : LMonoTy :=
  let args := t.typeArgs.map (fun elem => LMonoTy.ftvar elem)
  (.tcons t.name args)

inductive TypeDecl where
  | con : TypeConstructor → TypeDecl
  | syn : TypeSynonym → TypeDecl
  | data : List (LDatatype Visibility) → TypeDecl
  deriving Repr

instance : ToFormat TypeDecl where
  format d :=
    match d with
    | .con tc => f!"{tc}"
    | .syn ts => f!"{ts}"
    | .data [] => f!"<empty mutual block>"
    | .data [td] => f!"{td}"
    | .data tds => f!"mutual {Std.Format.joinSep (tds.map format) Format.line} end"

structure Axiom where
  name : BooleLabel
  e : LExpr BooleLParams.mono

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"

structure Procedure.Header where
  name     : BooleIdent
  typeArgs : List TyIdentifier
  inputs   : @LMonoTySignature Visibility
  outputs  : @LMonoTySignature Visibility
  deriving Repr, DecidableEq, Inhabited

instance : ToFormat Procedure.Header where
  format p :=
    let typeArgs := if p.typeArgs.isEmpty then f!"" else f!"∀{Format.joinSep p.typeArgs " "}."
    f!"procedure {p.name} : {typeArgs} ({Signature.format p.inputs}) → \
      ({Signature.format p.outputs})"

inductive Procedure.CheckAttr where
  | Free
  | Default
  deriving Repr, DecidableEq

instance : ToFormat Procedure.CheckAttr where
  format a :=
    match a with
    | .Default => f!""
    | _ => f!" (Attribute: {repr a})"

structure Procedure.Check where
  expr : Expression.Expr
  attr : CheckAttr := .Default
  md : Imperative.MetaData Expression := #[]
  deriving Repr, DecidableEq

instance : ToFormat Procedure.Check where
  format c := f!"{c.expr}{c.attr}"

structure Procedure.Spec where
  modifies       : List Expression.Ident
  preconditions  : ListMap BooleLabel Procedure.Check
  postconditions : ListMap BooleLabel Procedure.Check
  deriving Repr, DecidableEq, Inhabited

instance : ToFormat Procedure.Spec where
  format p :=
    f!"modifies: {format p.modifies}\n\
       preconditions: {format p.preconditions}\n\
       postconditions: {format p.postconditions}"

inductive CmdExt (P : PureExpr) where
  | cmd (c : Imperative.Cmd P)
  | call (lhs : List P.Ident) (procName : String) (args : List P.Expr)
         (md : MetaData P := .empty)

instance [ToFormat (Cmd P)] [ToFormat (MetaData P)]
    [ToFormat (List P.Ident)] [ToFormat (List P.Expr)] :
    ToFormat (CmdExt P) where
  format c := match c with
    | .cmd c => format c
    | .call lhs pname args md =>
      f!"{md}call " ++ (if lhs.isEmpty then f!"" else f!"{lhs} := ") ++
      f!"{pname}({args})"

abbrev Command := CmdExt Expression

inductive Stmt (P : PureExpr) (Cmd : Type) : Type where
  | cmd      (cmd : Cmd)
  | block    (label : String) (b : List (Stmt P Cmd)) (md : MetaData P := .empty)
  | ite      (cond : P.Expr)  (thenb : List (Stmt P Cmd)) (elseb : List (Stmt P Cmd)) (md : MetaData P := .empty)
  | loop     (guard : P.Expr) (measure : Option P.Expr) (invariant : Option P.Expr) (body : List (Stmt P Cmd)) (md : MetaData P := .empty)
  | for      (var : P.Ident) (tp : P.Ty) (init : P.Expr) (guard : P.Expr) (step : P.Expr) (measure : Option P.Expr) (invariant : Option P.Expr) (body : List (Stmt P Cmd)) (md : MetaData P := .empty)
  | forto    (dir : Bool) (var : P.Ident) (tp : P.Ty) (init : P.Expr) (limit : P.Expr) (step : Option P.Expr) (measure : Option P.Expr) (invariant : Option P.Expr) (body : List (Stmt P Cmd)) (md : MetaData P := .empty)
  -- | forEach  (elem : P.Ident) (arr : P.Expr) (invariant : Option P.Expr) (body : List (Stmt P Cmd))
        --  (md : MetaData P := .empty)
  | goto     (label : String) (md : MetaData P := .empty)
  | funcDecl (decl : PureFunc P) (md : MetaData P := .empty)
  deriving Inhabited

abbrev Block (P : PureExpr) (Cmd : Type) := List (Stmt P Cmd)

mutual

partial def formatStmt (P : PureExpr) (s : Stmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
  match s with
  | .cmd cmd => format cmd
  | .block label bl md => f!"{md}{label} : " ++ Format.bracket "{" f!"{formatBlock P bl}" "}"
  | .ite cond th el md => f!"{md}if {cond} then " ++
                        Format.bracket "{" f!"{formatBlock P th}" "}" ++
                        f!"{Format.line}else" ++
                        Format.bracket "{" f!"{formatBlock P el}" "}"
  | .loop guard measure invariant body md => f!"{md}while ({guard}) ({measure}) ({invariant}) " ++
                        Format.bracket "{" f!"{formatBlock P body}" "}"
  | .for var tp init guard step measure invariant body md => f!"{md}for (var {var} : {tp} := {init}; {guard}; {step}) ({measure}) ({invariant}) " ++
                        Format.bracket "{" f!"{formatBlock P body}" "}"
  | .forto dir var tp init limit step measure invariant body md => f!"{md}for {var} : {tp} := {init}; {if dir then "to" else "downto"} {limit} by {step} ({measure}) ({invariant}) " ++
                        Format.bracket "{" f!"{formatBlock P body}" "}"
  -- | .forEach elem arr invariant body md => f!"{md}for ({elem} : {arr}) ({invariant}) " ++
                        -- Format.bracket "{" f!"{formatBlock P body}" "}"
  | .goto label md => f!"{md}goto {label}"
  | .funcDecl _ md => f!"{md}funcDecl <function>"

partial def formatBlock (P : PureExpr) (bss : Block P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
    match bss with
    | [] => f!""
    | s :: rest => formatStmt P s ++
                   if rest.isEmpty then f!""
                   else f!"\n{formatBlock P rest}"

end

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (Stmt P C) where
  format s := formatStmt P s

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (Block P C) where
  format ss := formatBlock P ss

abbrev Statement := Stmt Boole.Expression Boole.Command

@[match_pattern]
abbrev Statement.init (name : Expression.Ident) (ty : Expression.Ty) (expr : Expression.Expr)
    (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.init name ty expr md))
@[match_pattern]
abbrev Statement.set (name : Expression.Ident) (expr : Expression.Expr)
    (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name expr md))
@[match_pattern]
abbrev Statement.havoc (name : Expression.Ident) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.havoc name md))
@[match_pattern]
abbrev Statement.assert (label : String) (b : Expression.Expr) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assert label b md))
@[match_pattern]
abbrev Statement.assume (label : String) (b : Expression.Expr) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assume label b md))
@[match_pattern]
abbrev Statement.cover (label : String) (b : Expression.Expr) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.cover label b md))
@[match_pattern]
abbrev Statement.call (lhs : List Expression.Ident) (pname : String) (args : List Expression.Expr)
    (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.call lhs pname args md)
@[match_pattern]
abbrev Statement.block (label : String) (b : Block Expression Command)
    (md : MetaData Expression := .empty) :=
  @Stmt.block Expression Command label b md

structure Procedure where
  header : Procedure.Header
  spec   : Procedure.Spec
  body   : List Statement
  deriving Inhabited

instance : ToFormat Procedure where
  format p :=
    f!"({p.header})\n\
       {p.spec}\n\
       body: {p.body}\n"

abbrev Function := Lambda.LFunc BooleLParams

instance : DecidableEq BooleLParams.IDMeta :=
  show DecidableEq Visibility from inferInstance

instance : ToFormat BooleLParams.IDMeta :=
  show ToFormat Visibility from inferInstance

inductive Decl where
  | var (name : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr) (md : MetaData Boole.Expression := .empty)
  | type (t : TypeDecl) (md : MetaData Boole.Expression := .empty)
  | ax   (a : Axiom) (md : MetaData Boole.Expression := .empty)
  | distinct (name : Expression.Ident) (es : List Expression.Expr) (md : MetaData Boole.Expression := .empty)
  | proc (d : Procedure) (md : MetaData Boole.Expression := .empty)
  | func (f : Function) (md : MetaData Boole.Expression := .empty)
  deriving Inhabited

instance : ToFormat Decl where
  format d := match d with
    | .var name ty e md => f!"{md}var ({name} : {ty}) := {e}"
    | .type t md => f!"{md}{t}"
    | .ax a md  => f!"{md}{a}"
    | .distinct l es md  => f!"{md}distinct [{l}] {es}"
    | .proc p md => f!"{md}{p}"
    | .func f md => f!"{md}{f}"

abbrev Decls := List Decl

structure Program where
  { decls : Decls }

def Program.init : Program :=
  { decls := [] }

instance : ToFormat Program where
  format p := Std.Format.joinSep (List.map format p.decls) Format.line

instance : Inhabited Program where
  default := .init

end Strata.Boole
