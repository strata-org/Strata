/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
-- B3AST DDM Dialect for Abstract Syntax Tree
---------------------------------------------------------------------

/-!
# B3 Abstract Syntax Tree (AST)

The B3 AST differs from the B3 CST in two ways. First, the AST uses de Bruijn indices for
variable references instead of identifier names. Where the CST parses `i` and `old i` as
distinct identifiers, the AST represents both as de Bruijn bound variables. Second, where
the CST has multiple syntactic forms for the same semantic construct, the AST has a single
canonical representation.

The CST is suitable for parsing and pretty-printing the B3 language, while the AST is
suitable as a target for encoding Strata Core. The bidirectional conversion in
`Conversion.lean` handles name resolution, de Bruijn index assignment, and special cases
like shadowed variables and `inout` parameters (modeled as two context values). Conversions
return a list of errors for issues like unresolved identifiers or out-of-bounds references.
-/

#dialect
dialect B3AST;

category Literal;
category Expression;
category Pattern;
category BinaryOp;
category UnaryOp;
category QuantifierKind;

op intLit (@[unwrap] n : Num) : Literal => n;
op boolLit (@[unwrap] b : Bool) : Literal => b;
op stringLit (@[unwrap] s : Str) : Literal => s;

op iff : BinaryOp => "iff";
op implies : BinaryOp => "implies";
op impliedBy : BinaryOp => "impliedBy";
op and : BinaryOp => "and";
op or : BinaryOp => "or";
op eq : BinaryOp => "eq";
op neq : BinaryOp => "neq";
op lt : BinaryOp => "lt";
op le : BinaryOp => "le";
op ge : BinaryOp => "ge";
op gt : BinaryOp => "gt";
op add : BinaryOp => "add";
op sub : BinaryOp => "sub";
op mul : BinaryOp => "mul";
op div : BinaryOp => "div";
op mod : BinaryOp => "mod";

op not : UnaryOp => "not";
op neg : UnaryOp => "neg";

op forall : QuantifierKind => "forall";
op exists : QuantifierKind => "exists";

op literal (val : Literal) : Expression => "#" val;
op id (@[unwrap] index : Num) : Expression => index;
op ite (cond : Expression, thn : Expression, els : Expression) : Expression =>
  "ite " cond " " thn " " els;
op binaryOp (binOp : BinaryOp, lhs : Expression, rhs : Expression) : Expression =>
  "binop " binOp " " lhs " " rhs;
op unaryOp (unOp : UnaryOp, arg : Expression) : Expression =>
  "unop " unOp " " arg;
op functionCall (fnName : Ident, args : CommaSepBy Expression) : Expression =>
  "call " fnName " (" args ")";
op labeledExpr (label : Ident, expr : Expression) : Expression =>
  "labeled " label " " expr;
op letExpr (var : Ident, value : Expression, body : Expression) : Expression =>
  "let " var " = " value " in " body;
category VarDecl;
op quantVarDecl (name : Ident, ty : Ident) : VarDecl =>
  name " : " ty;

op quantifierExpr (quantifier : QuantifierKind, vars : Seq VarDecl, patterns : Seq Pattern, body : Expression) : Expression =>
  "quant " quantifier " [" vars "] [" patterns "] " body;

op pattern (exprs : CommaSepBy Expression) : Pattern =>
  "pattern (" exprs ")";

category Statement;
category CallArg;
category OneIfCase;

op varDecl (name : Ident, ty : Option Ident, autoinv : Option Expression, init : Option Expression) : Statement =>
  "varDecl " name " : " ty " autoinv " autoinv " := " init;
op assign (lhs : Num, rhs : Expression) : Statement =>
  "assign @" lhs " := " rhs;
op reinit (name : Num) : Statement =>
  "reinit @" name;
op blockStmt (stmts : Seq Statement) : Statement =>
  "block {" stmts "}";
op call (procName : Ident, args : Seq CallArg) : Statement =>
  "call " procName "(" args ")";
op check (expr : Expression) : Statement =>
  "check " expr;
op assume (expr : Expression) : Statement =>
  "assume " expr;
op reach (expr : Expression) : Statement =>
  "reach " expr;
op assert (expr : Expression) : Statement =>
  "assert " expr;
op aForall (var : Ident, ty : Ident, body : Statement) : Statement =>
  "forall " var " : " ty " " body;
op choose (branches : Seq Statement) : Statement =>
  "choose " branches;
op ifStmt (cond : Expression, thenBranch : Statement, elseBranch : Option Statement) : Statement =>
  "if " cond " then " thenBranch " else " elseBranch;
op oneIfCase (cond : Expression, body : Statement): OneIfCase =>
  "oneIfCase " cond body;
op ifCase (cases : Seq OneIfCase) : Statement =>
  "ifcase " cases;
op loop (invariants : Seq Expression, body : Statement) : Statement =>
  "loop invariants " invariants " {" body "}";
op labeledStmt (label : Ident, stmt : Statement) : Statement =>
  "labelStmt " label " " stmt;
op exit (label : Option Ident) : Statement =>
  "exit " label;
op returnStmt : Statement =>
  "return";
op probe (label : Ident) : Statement =>
  "probe " label;

op callArgExpr (e : Expression) : CallArg =>
  "expr " e;
op callArgOut (id : Ident) : CallArg =>
  "out " id;
op callArgInout (id : Ident) : CallArg =>
  "inout " id;

category ParamMode;
category FParameter;
category PParameter;
category Spec;
category Decl;

op paramModeIn : ParamMode => "in";
op paramModeOut : ParamMode => "out";
op paramModeInout : ParamMode => "inout";

op fParameter (injective : Bool, name : Ident, ty : Ident) : FParameter =>
  "fparam " injective " " name " : " ty;

op pParameter (mode : ParamMode, name : Ident, ty : Ident, autoinv : Option Expression) : PParameter =>
  "pparam " mode " " name " : " ty " autoinv " autoinv;

op specRequires (expr : Expression) : Spec =>
  "requires " expr;
op specEnsures (expr : Expression) : Spec =>
  "ensures " expr;

op typeDecl (name : Ident) : Decl =>
  "type " name;
op tagger (name : Ident, forType : Ident) : Decl =>
  "tagger " name " for " forType;

category When;
op when (cond: Expression): When =>
  "when " cond;

category FunctionBody;
op functionBody (whens: Seq When, body: Expression): FunctionBody =>
  whens "{" body "}";

op function (name : Ident, params : Seq FParameter, resultType : Ident, tag : Option Ident, body : Option FunctionBody) : Decl =>
  "\nfunction " name " (" params ") : " resultType " tag " tag " body " body;

op axiom (explains : Seq Ident, expr : Expression) : Decl =>
  "\naxiom explains " explains "," expr;

op procedure (name : Ident, params : Seq PParameter, specs : Seq Spec, body : Option Statement) : Decl =>
  "\nprocedure " name " (" params ") specs " specs " body " body;

category Program;
op program (decls : Seq Decl) : Program =>
  decls;

#end

namespace B3AST

#strata_gen B3AST

end B3AST

---------------------------------------------------------------------
-- Metadata Transformation
---------------------------------------------------------------------

namespace B3AST

open Strata.B3AST

private def mapAnn {α M N : Type} (f : M → N) (a : Ann α M) : Ann α N :=
  ⟨f a.ann, a.val⟩

def Literal.mapMetadata [Inhabited N] (f : M → N) : Literal M → Literal N
  | .intLit m n => .intLit (f m) n
  | .boolLit m b => .boolLit (f m) b
  | .stringLit m s => .stringLit (f m) s

def BinaryOp.mapMetadata [Inhabited N] (f : M → N) : BinaryOp M → BinaryOp N
  | .iff m => .iff (f m)
  | .implies m => .implies (f m)
  | .impliedBy m => .impliedBy (f m)
  | .and m => .and (f m)
  | .or m => .or (f m)
  | .eq m => .eq (f m)
  | .neq m => .neq (f m)
  | .lt m => .lt (f m)
  | .le m => .le (f m)
  | .ge m => .ge (f m)
  | .gt m => .gt (f m)
  | .add m => .add (f m)
  | .sub m => .sub (f m)
  | .mul m => .mul (f m)
  | .div m => .div (f m)
  | .mod m => .mod (f m)

def UnaryOp.mapMetadata [Inhabited N] (f : M → N) : UnaryOp M → UnaryOp N
  | .not m => .not (f m)
  | .neg m => .neg (f m)

def QuantifierKind.mapMetadata [Inhabited N] (f : M → N) : QuantifierKind M → QuantifierKind N
  | .forall m => .forall (f m)
  | .exists m => .exists (f m)

def VarDecl.mapMetadata [Inhabited N] (f : M → N) : VarDecl M → VarDecl N
  | .quantVarDecl m name ty => .quantVarDecl (f m) (mapAnn f name) (mapAnn f ty)

mutual

def Expression.mapMetadata [Inhabited N] (f : M → N) (e: Expression M) :Expression N :=
  match e with
  | .literal m lit => .literal (f m) (Literal.mapMetadata f lit)
  | .id m idx => .id (f m) idx
  | .ite m cond thn els => .ite (f m) (Expression.mapMetadata f cond) (Expression.mapMetadata f thn) (Expression.mapMetadata f els)
  | .binaryOp m op lhs rhs => .binaryOp (f m) (BinaryOp.mapMetadata f op) (Expression.mapMetadata f lhs) (Expression.mapMetadata f rhs)
  | .unaryOp m op arg => .unaryOp (f m) (UnaryOp.mapMetadata f op) (Expression.mapMetadata f arg)
  | .functionCall m fnName args => .functionCall (f m) (mapAnn f fnName) ⟨f args.ann, args.val.map (Expression.mapMetadata f)⟩
  | .labeledExpr m label expr => .labeledExpr (f m) (mapAnn f label) (Expression.mapMetadata f expr)
  | .letExpr m var value body => .letExpr (f m) (mapAnn f var) (Expression.mapMetadata f value) (Expression.mapMetadata f body)
  | .quantifierExpr m qkind vars patterns body =>
      .quantifierExpr (f m) (QuantifierKind.mapMetadata f qkind)
        ⟨f vars.ann, vars.val.map (VarDecl.mapMetadata f)⟩
        ⟨f patterns.ann, patterns.val.map (fun p =>
          match _: p with
          | .pattern m exprs => .pattern (f m) ⟨f exprs.ann, exprs.val.map (Expression.mapMetadata f)⟩)⟩
        (Expression.mapMetadata f body)
  termination_by SizeOf.sizeOf e
  decreasing_by
    all_goals (simp_wf <;> try omega)
    . cases args ; simp_all
      rename_i h; have := Array.sizeOf_lt_of_mem h; omega
    . cases exprs; cases patterns; simp_all; subst_vars
      rename_i h1 h2
      have := Array.sizeOf_lt_of_mem h1
      have Hpsz := Array.sizeOf_lt_of_mem h2
      simp at Hpsz; omega

def CallArg.mapMetadata [Inhabited N] (f : M → N) : CallArg M → CallArg N
  | .callArgExpr m e => .callArgExpr (f m) (Expression.mapMetadata f e)
  | .callArgOut m id => .callArgOut (f m) (mapAnn f id)
  | .callArgInout m id => .callArgInout (f m) (mapAnn f id)

def Statement.mapMetadata [Inhabited N] (f : M → N) (s: Statement M) : Statement N :=
  match s with
  | .varDecl m name ty autoinv init =>
      .varDecl (f m) (mapAnn f name)
        ⟨f ty.ann, ty.val.map (mapAnn f)⟩
        ⟨f autoinv.ann, autoinv.val.map (Expression.mapMetadata f)⟩
        ⟨f init.ann, init.val.map (Expression.mapMetadata f)⟩
  | .assign m lhs rhs => .assign (f m) (mapAnn f lhs) (Expression.mapMetadata f rhs)
  | .reinit m idx => .reinit (f m) (mapAnn f idx)
  | .blockStmt m stmts => .blockStmt (f m) ⟨f stmts.ann, stmts.val.map (Statement.mapMetadata f)⟩
  | .call m procName args => .call (f m) (mapAnn f procName) ⟨f args.ann, args.val.map (CallArg.mapMetadata f)⟩
  | .check m expr => .check (f m) (Expression.mapMetadata f expr)
  | .assume m expr => .assume (f m) (Expression.mapMetadata f expr)
  | .reach m expr => .reach (f m) (Expression.mapMetadata f expr)
  | .assert m expr => .assert (f m) (Expression.mapMetadata f expr)
  | .aForall m var ty body => .aForall (f m) (mapAnn f var) (mapAnn f ty) (Statement.mapMetadata f body)
  | .choose m branches => .choose (f m) ⟨f branches.ann, branches.val.map (Statement.mapMetadata f)⟩
  | .ifStmt m cond thenB elseB =>
      .ifStmt (f m) (Expression.mapMetadata f cond) (Statement.mapMetadata f thenB)
      -- Unlike List and Array, Option.map does not use `attach` by default for wf proofs
        ⟨f elseB.ann, elseB.val.attach.map (fun x => Statement.mapMetadata f x.1)⟩
  | .ifCase m cases => .ifCase (f m) ⟨f cases.ann, cases.val.map (fun o =>
      match ho: o with
      | .oneIfCase m cond body => .oneIfCase (f m) (Expression.mapMetadata f cond) (Statement.mapMetadata f body))⟩
  | .loop m invariants body =>
      .loop (f m) ⟨f invariants.ann, invariants.val.map (Expression.mapMetadata f)⟩ (Statement.mapMetadata f body)
  | .labeledStmt m label stmt => .labeledStmt (f m) (mapAnn f label) (Statement.mapMetadata f stmt)
  | .exit m label => .exit (f m) ⟨f label.ann, label.val.map (mapAnn f)⟩
  | .returnStmt m => .returnStmt (f m)
  | .probe m label => .probe (f m) (mapAnn f label)
  decreasing_by
    all_goals (simp_wf; try omega)
    . cases stmts; simp_all; subst_vars
      rename_i h; have :=Array.sizeOf_lt_of_mem h; omega
    . cases branches; simp_all; subst_vars
      rename_i h; have :=Array.sizeOf_lt_of_mem h; omega
    . cases elseB; cases x
      case mk x xin =>
        simp_all; subst_vars; simp; omega
    . cases cases; simp_all; subst_vars
      rename_i h; have :=Array.sizeOf_lt_of_mem h; simp_all; omega

def ParamMode.mapMetadata [Inhabited N] (f : M → N) : ParamMode M → ParamMode N
  | .paramModeIn m => .paramModeIn (f m)
  | .paramModeOut m => .paramModeOut (f m)
  | .paramModeInout m => .paramModeInout (f m)

def FParameter.mapMetadata [Inhabited N] (f : M → N) : FParameter M → FParameter N
  | .fParameter m injective name ty => .fParameter (f m) (mapAnn f injective) (mapAnn f name) (mapAnn f ty)

def PParameter.mapMetadata [Inhabited N] (f : M → N) : PParameter M → PParameter N
  | .pParameter m mode name ty autoinv =>
      .pParameter (f m) (ParamMode.mapMetadata f mode) (mapAnn f name) (mapAnn f ty)
        ⟨f autoinv.ann, autoinv.val.map (Expression.mapMetadata f)⟩

def Spec.mapMetadata [Inhabited N] (f : M → N) : Spec M → Spec N
  | .specRequires m expr => .specRequires (f m) (Expression.mapMetadata f expr)
  | .specEnsures m expr => .specEnsures (f m) (Expression.mapMetadata f expr)

def When.mapMetadata [Inhabited N] (f : M → N) : When M → When N
  | .when m cond => .when (f m) (Expression.mapMetadata f cond)

def FunctionBody.mapMetadata [Inhabited N] (f : M → N) : FunctionBody M → FunctionBody N
  | .functionBody m whens body =>
      .functionBody (f m) ⟨f whens.ann, whens.val.map (When.mapMetadata f)⟩ (Expression.mapMetadata f body)

def Decl.mapMetadata [Inhabited N] (f : M → N) : Decl M → Decl N
  | .typeDecl m name => .typeDecl (f m) (mapAnn f name)
  | .tagger m name forType => .tagger (f m) (mapAnn f name) (mapAnn f forType)
  | .function m name params resultType tag body =>
      .function (f m) (mapAnn f name) ⟨f params.ann, params.val.map (FParameter.mapMetadata f)⟩
        (mapAnn f resultType) ⟨f tag.ann, tag.val.map (mapAnn f)⟩
        ⟨f body.ann, body.val.map (FunctionBody.mapMetadata f)⟩
  | .axiom m explains expr =>
      .axiom (f m) ⟨f explains.ann, explains.val.map (mapAnn f)⟩ (Expression.mapMetadata f expr)
  | .procedure m name params specs body =>
      .procedure (f m) (mapAnn f name) ⟨f params.ann, params.val.map (PParameter.mapMetadata f)⟩
        ⟨f specs.ann, specs.val.map (Spec.mapMetadata f)⟩
        ⟨f body.ann, body.val.map (Statement.mapMetadata f)⟩

def Program.mapMetadata [Inhabited N] (f : M → N) : Program M → Program N
  | .program m decls => .program (f m) ⟨f decls.ann, decls.val.map (Decl.mapMetadata f)⟩

end

def Expression.toUnit [Inhabited (Expression Unit)] (e : Expression M) : Expression Unit :=
  e.mapMetadata (fun _ => ())

def Statement.toUnit [Inhabited (Expression Unit)] (s : Statement M) : Statement Unit :=
  s.mapMetadata (fun _ => ())

def Decl.toUnit [Inhabited (Expression Unit)] (d : Decl M) : Decl Unit :=
  d.mapMetadata (fun _ => ())

def Program.toUnit [Inhabited (Expression Unit)] (p : Program M) : Program Unit :=
  p.mapMetadata (fun _ => ())

end B3AST
