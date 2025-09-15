/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Very rough dialect with some Boogie-like code for example purposes.
import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

namespace Strata

namespace OfAstM

def argAsExpr (arg : Arg) : OfAstM Expr :=
    match arg with
    | .expr e => pure e
    | _ => .throwExpectedExpr arg

end OfAstM

structure DialectElabContext where
  dialectMap : DialectMap
  openDialectSet : Std.HashSet DialectName
  tokenTable : Lean.Parser.TokenTable
  parsingTables : PrattParsingTableMap
  typeOrCatDeclMap : Elab.TypeOrCatDeclMap
  metadataDeclMap : Elab.MetadataDeclMap
  syntaxElabMap : Elab.SyntaxElabMap

namespace DialectElabContext

def fromDialects (dialects : List Dialect) : DialectElabContext :=
  let count := dialects.length
  let (tokenTable, parsingTables) : Lean.Parser.TokenTable × PrattParsingTableMap :=
    dialects.foldl (init := ({}, {})) fun (tokens, m) d =>
      match Elab.initParsers.mkDialectParsers d with
      | .error msg =>
        panic s!"Could not add open dialect: {eformat msg |>.pretty}"
      | .ok parsers =>
        let tokens := parsers.foldl (init := tokens) (·.addParser ·.parser)
        let m := m.addDialect! d parsers
        (tokens, m)
  {
    dialectMap := DialectMap.ofList! dialects
    openDialectSet := dialects.foldl (init := .emptyWithCapacity count) (·.insert ·.name)
    tokenTable := tokenTable
    parsingTables := parsingTables
    typeOrCatDeclMap := dialects.foldl (init := {}) (·.addDialect ·)
    metadataDeclMap := dialects.foldl (init := {}) (·.addDialect ·)
    syntaxElabMap := dialects.foldl (init := {}) (·.addDialect ·)
  }

def mkElabContext (ctx : DialectElabContext) (gctx : GlobalContext) (ictx : Parser.InputContext)
    : Elab.ElabContext := {
  dialects := ctx.dialectMap
  openDialectSet := ctx.openDialectSet
  typeOrCatDeclMap := ctx.typeOrCatDeclMap
  metadataDeclMap := ctx.metadataDeclMap
  globalContext := gctx
  inputContext := ictx
  syntaxElabs := ctx.syntaxElabMap
}

end DialectElabContext

open Lean.Parser (InputContext)
open Elab (TypingContext)

class GenType (α : Type _) where
  dialectInfo : DialectElabContext
  toArg : α → Arg
  ofArg : InputContext -> TypingContext -> Lean.Syntax -> Except (Array Lean.Message) α

namespace GenType

def ofExprImpl (elabGen : DialectElabContext) (ofExpr : Expr → OfAstM α) (ictx : InputContext) (tctx : Elab.TypingContext ) (stx : Lean.Syntax) : Except (Array Lean.Message) α := do
    let elabCtx : Elab.ElabContext := elabGen.mkElabContext tctx.globalContext ictx
    let elabState : Elab.ElabState := { errors := #[] }
    let (t, s) := Elab.elabExpr tctx stx elabCtx elabState
    if s.errors.isEmpty then
      match ofExpr t.info.asExpr!.expr with
      | .error e => throw #[Lean.mkStringMessage ictx (stx.getPos?.getD 0) e]
      | .ok v => pure v
    else
      throw <| s.errors.map (·.snd)

def ofTypeImpl (elabGen : DialectElabContext) (ofType : TypeExpr → OfAstM α) (ictx : InputContext) (tctx : Elab.TypingContext ) (stx : Lean.Syntax) : Except (Array Lean.Message) α := do
  let elabCtx : Elab.ElabContext := elabGen.mkElabContext tctx.globalContext ictx
  let elabState : Elab.ElabState := { errors := #[] }
  let (t, s) := Elab.elabExpr tctx stx elabCtx elabState
  if s.errors.isEmpty then
    match ofType t.info.asType!.typeExpr with
    | .error e => throw #[Lean.mkStringMessage ictx (stx.getPos?.getD 0) e]
    | .ok v => pure v
  else
    throw <| s.errors.map (·.snd)

def format {α} [h : GenType α] (a : α) (ctx : GlobalContext := {}) (opts : FormatOptions := {}) (bindings : Array String := #[]) : String :=
  let fctx : FormatContext := .ofDialects h.dialectInfo.dialectMap ctx opts
  let fs : FormatState := { openDialects := h.dialectInfo.openDialectSet, bindings }
  toString (mformat (GenType.toArg a) fctx fs).format

def parse (α : Type) [h : GenType α] (leanEnv : Lean.Environment) (tctx : Elab.TypingContext)
      (inputCtx : Lean.Parser.InputContext) (pos stopPos : String.Pos) : Except (Array Lean.Message) α :=
  let tt : Lean.Parser.TokenTable := h.dialectInfo.tokenTable
  let parsingTableMap : PrattParsingTableMap := h.dialectInfo.parsingTables
  let cat : QualifiedIdent := q`Init.Expr
  let leanParserState := Parser.runCatParser tt parsingTableMap leanEnv inputCtx pos stopPos cat
  let errors : Array Lean.Message :=
        leanParserState.allErrors.map fun (pos, stk, err) =>
          Lean.mkErrorMessage inputCtx pos stk err
  let errors :=
      if leanParserState.pos < stopPos then
        errors.push (Lean.mkStringMessage inputCtx leanParserState.pos s!"Unexpected character.")
      else
        errors
  if !errors.isEmpty then
    .error errors
  else if leanParserState.stxStack.size == 0 then
    panic! "Cmmand state is empty"
  else if leanParserState.stxStack.size > 1 then
    panic! "Command state has multiple entries."
  else
    let stx := leanParserState.stxStack.back
    GenType.ofArg inputCtx tctx stx

def parseString (α : Type) [h : GenType α] (leanEnv : Lean.Environment) (contents : String) (tctx : Elab.TypingContext := default) : Except (Array Lean.Message) α := do
  let ictx := Parser.stringInputContext contents
  parse α leanEnv tctx ictx 0 contents.endPos

end GenType

#dialect
dialect Arith;

type Bool;

fn btrue : Bool => "true";
fn bfalse : Bool => "false";
fn imp (a : Bool, c : Bool) : Bool => @[prec(15), rightassoc] a " ==> " c;

type Int;
fn intLit (n : Num) : Int => n;
fn add (x : Int, y : Int) : Int => @[prec(25), leftassoc] x " + " y;
fn mul (x : Int, y : Int) : Int => @[prec(25), leftassoc] x " * " y;

fn eq (tp : Type, x : tp, y : tp) : Bool => @[prec(20)] x " == " y;
fn le (x : Int, y : Int) : Bool => @[prec(20)] x " <= " y;
fn lt (x : Int, y : Int) : Bool => @[prec(20)] x " > " y;
fn ge (x : Int, y : Int) : Bool => @[prec(20)] x " >= " y;
fn gt (x : Int, y : Int) : Bool => @[prec(20)] x " > " y;
#end


namespace Arith

--set_option trace.Strata.generator true
-- set_option trace.Strata.DDM.syntax true
#strata_gen Arith
--set_option trace.Strata.generator false


def arithDialects : DialectMap := DialectMap.ofList! [initDialect, Arith]



def arithDialectParsingContext :=
  DialectElabContext.fromDialects [initDialect, Arith]

namespace ArithType

instance : GenType ArithType where
  dialectInfo := arithDialectParsingContext
  toArg a := .type a.toAst
  ofArg := GenType.ofTypeImpl arithDialectParsingContext ArithType.ofAst

end ArithType

namespace ArithType

instance : GenType ArithType where
  dialectInfo := arithDialectParsingContext
  toArg a := .type a.toAst
  ofArg := GenType.ofTypeImpl arithDialectParsingContext ArithType.ofAst

end ArithType


namespace Expr

instance : GenType Expr where
  dialectInfo := arithDialectParsingContext
  toArg a := .expr a.toAst
  ofArg := GenType.ofExprImpl arithDialectParsingContext Expr.ofAst

end Expr



--instance : Repr Lean.MessageData where
--  reprPrec _ _ := "MessageData"


def render [Repr α] (me : Except ε α) : String :=
  match me with
  | .error _ => "ERROR"
  | .ok e => toString (reprPrec e 0)

/--
info: "true"
-/
#guard_msgs in
#eval GenType.format Expr.btrue

/--
info: "ERROR"
-/
#guard_msgs in
#eval do
  let env ← Lean.mkEmptyEnvironment 0
  return render <| GenType.parseString Expr env "false true"

/--
info: "Strata.Arith.Expr.imp (Strata.Arith.Expr.bfalse) (Strata.Arith.Expr.btrue)"
-/
#guard_msgs in
#eval do
  let env ← Lean.mkEmptyEnvironment 0
  return render <| GenType.parseString Expr env "false ==> true"

end Arith


#dialect
dialect ArithChecker;
import Arith;

op assert (p : Bool) : Command => "assert " p ";\n";
op check_sat : Command => "check_sat" ";\n";
#end

namespace ArithChecker

#strata_gen ArithChecker

end ArithChecker

#dialect
dialect ArithFn;
import Arith;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : Type) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category Statement;
category Block;

@[declare(v, tp)]
op assign (tp : Type, v : Ident, a : tp) : Statement => "assign" "(" v:40 ", " a:40 ")" ";\n";
op if (c : Bool, t : Block, f : Block) : Statement => "if " "(" c:0 ")" t:50 "else " f:50;

op block (c : Seq Statement) : Block => " {\n" indent(2, c:40) "}\n";

op procedure (name : Ident, b : Bindings, @[scope(b)] c : Block) : Command => @[prec(10)] "procedure " name b c;
#end

def example1 := #strata
program ArithChecker;
assert true;
assert (true ==> true) ==> true;
assert true ==> (true ==> true);
#end

/--
info: program ArithChecker;
assert true;
assert (true ==> true) ==> true;
assert true ==> true ==> true;
-/
#guard_msgs in
#eval IO.println <| example1.format |>.render

def example2 :=
#strata
program ArithFn;
procedure add (x : Int, y : Int, c : Bool) {
  assign(a, c);
  if (a) {
    assign(b, a);
    assign(c, b);
  } else {
    assign(b, a);
    assign(c, b);
  }
}
#end

/--
info: program ArithFn;
procedure add(x:Int, y:Int, c:Bool) {
  assign(a, c);
  if (a) {
    assign(b, a);
    assign(c, b);
  }
  else  {
    assign(b, a);
    assign(c, b);
  }
}
-/
#guard_msgs in
#eval IO.println <| example2.format |>.render
