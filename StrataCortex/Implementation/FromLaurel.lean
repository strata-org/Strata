/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelToCoreSchemaPass
public import StrataLaurel.Implementation.MapStmtExpr
public import StrataLaurel.Implementation.LaurelTypes
public import StrataLaurel.Implementation.CoreDefinitionsForLaurel
public import Strata.Languages.Cortex.Module

namespace Cortex.FromLaurel

open Strata Strata.Laurel
open Imperative Lambda
open Cortex (Expr IRCmd MD LBlock mkFvar)

public section

structure Blk where
  label : String
  cmds : Array IRCmd := #[]
  region : Option Nat := none

structure Frame where
  name : String
  start : String
  stop : String
  finDepth : Nat

structure Final where
  body : StmtExprMd
  outer : Option Nat

structure HInfo where
  id : Nat
  binder : String
  target : String

structure CState where
  sealed : Array (String × LBlock × Option Nat) := #[]
  cur : Blk
  fresh : Nat := 0
  frames : List Frame := []
  finals : List Final := []
  handlers : Array HInfo := #[]
  locals : Array (String × LTy) := #[]
  retLabel : String := "$return"
  outputs : List String := []
  procNames : Std.HashSet String := {}
  prelude : Std.HashSet String := {}
  preludeProcs : List Strata.Laurel.Procedure := []
  composites : List CompositeType := []
  uncheck : Bool := true

abbrev CM := StateT CState TranslateM

def unsupported (src : FileRange) (what : String) : CM Unit :=
  emitDiagnostic (diagnosticFromSource src s!"Cortex does not support {what}" MessageKind.notYetImplemented)

def freshLabel (base : String) : CM String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{base}${s.fresh}"

def emit (c : IRCmd) : CM Unit :=
  modify fun s => { s with cur := { s.cur with cmds := s.cur.cmds.push c } }

def sealWith (tr : DetTransferCmd Cortex.Label Core.Expression) (next : String) : CM Unit :=
  modify fun s =>
    let blk : LBlock := { cmds := s.cur.cmds.toList, transfer := tr }
    { s with sealed := s.sealed.push (s.cur.label, blk, s.cur.region),
             cur := { label := next, region := s.cur.region } }

def jumpTo (l : String) : CM Unit := do
  sealWith (.goto l) (← freshLabel "$dead")

def fallInto (l : String) : CM Unit := sealWith (.goto l) l

def switchTo (l : String) : CM Unit := sealWith (.finish .empty) l

def idents (l : List String) : List Core.Expression.Ident := l.map fun n => ⟨n, ()⟩

def deadEnd : CM Unit := do
  sealWith (.finish .empty) (← freshLabel "$dead")

def setRegion (r : Option Nat) : CM Unit := do
  let l ← freshLabel "$region"
  fallInto l
  modify fun s => { s with cur := { s.cur with region := r } }

def isPrimName (n : String) : Bool :=
  n == "int" || n == "bool" || n == "string" || n == "real"

partial def substHigh (σ : List (String × HighTypeMd)) (t : HighTypeMd) : HighTypeMd :=
  match t.val with
  | .UserDefined n => (σ.lookup n.text).getD t
  | .TVar n => (σ.lookup n.text).getD t
  | .Applied b args => { t with val := .Applied (substHigh σ b) (args.map (substHigh σ)) }
  | .TSet e => { t with val := .TSet (substHigh σ e) }
  | .TMap k v => { t with val := .TMap (substHigh σ k) (substHigh σ v) }
  | _ => t

partial def unfoldAlias (model : SemanticModel) (t : HighTypeMd) (fuel : Nat := 32) : HighTypeMd :=
  match fuel with
  | 0 => t
  | fuel + 1 =>
  match t.val with
  | .UserDefined n =>
    match model.get? n with
    | some (.typeAlias a) => unfoldAlias model a.target fuel
    | _ => t
  | .Applied b args =>
    match b.val with
    | .UserDefined n =>
      match model.get? n with
      | some (.typeAlias a) =>
        unfoldAlias model (substHigh ((a.typeArgs.map (·.text)).zip args) a.target) fuel
      | _ => { t with val := .Applied b (args.map (unfoldAlias model · fuel)) }
    | _ => t
  | .TSet e => { t with val := .TSet (unfoldAlias model e fuel) }
  | .TMap k v => { t with val := .TMap (unfoldAlias model k fuel) (unfoldAlias model v fuel) }
  | _ => t

def lty (t : HighTypeMd) : CM LTy := do
  let model := (← getThe TranslateState).model
  let t := unfoldAlias model t
  match t.val with
  | .UserDefined n =>
    if isPrimName n.text then return .forAll [] (← translateType t) else
    if n.text.startsWith "$Any" then return .forAll [] (.tcons n.text []) else
    match model.get? n with
    | some (.compositeType c) => return .forAll [] (.tcons c.name.text [])
    | some (.constrainedType c) => return .forAll [] (.tcons c.name.text [])
    | _ => return .forAll [] (← translateType t)
  | .Applied base _ =>
    match base.val with
    | .UserDefined n =>
      match model.get? n with
      | some (.compositeType _) =>
        unsupported t.source "generic composite types"
        return .forAll [] (.tcons n.text [])
      | _ => return .forAll [] (← translateType t)
    | _ => return .forAll [] (← translateType t)
  | _ => return .forAll [] (← translateType t)

def declLocal (name : String) (ty : LTy) : CM Unit := do
  let s ← get
  unless s.locals.any (·.1 == name) do
    set { s with locals := s.locals.push (name, ty) }

partial def baseHigh (model : SemanticModel) (t : HighTypeMd) (fuel : Nat := 16) : HighTypeMd :=
  match fuel, t.val with
  | 0, _ => t
  | fuel + 1, .UserDefined n =>
    match model.get? n with
    | some (.constrainedType c) => baseHigh model c.base fuel
    | some (.typeAlias a) => baseHigh model a.target fuel
    | _ => t
  | _, _ => t

def freshTemp (ty : HighTypeMd) (src : FileRange) : CM Identifier := do
  let ty := baseHigh (← getThe TranslateState).model ty
  let ts ← getThe TranslateState
  let id := ts.model.nextId
  let s ← get
  set { s with fresh := s.fresh + 1 }
  let ident : Identifier := { text := s!"$c{s.fresh}", uniqueId := some id, source := src }
  modifyThe TranslateState fun ts =>
    { ts with model := { ts.model with
        refToDef := ts.model.refToDef.insert id (.var ident ty), nextId := id + 1 } }
  declLocal ident.text (← lty ty)
  return ident

def varNode (i : Identifier) (src : FileRange) : StmtExprMd := { val := .Var (.Local i), source := src }

def isProcCallee (model : SemanticModel) (procNames : Std.HashSet String) (callee : Identifier) : Bool :=
  match model.get? callee with
  | some (.staticProcedure p) => procNames.contains p.name.text
  | some (.instanceProcedure _ _) => true
  | _ => false

def calleeInfo (callee : Identifier) : CM (String × List Parameter) := do
  match (← getThe TranslateState).model.get? callee with
  | some (.staticProcedure p) => return (p.name.text, p.outputs)
  | some (.instanceProcedure t p) => return (s!"{t.text}${p.name.text}", p.outputs)
  | _ => return (callee.text, [])

def preludePre? (model : SemanticModel) (prelude : Std.HashSet String) (callee : Identifier) :
    Option Strata.Laurel.Procedure :=
  match model.get? callee with
  | some (.staticProcedure p) =>
    if prelude.contains p.name.text && p.preconditions.any (·.mode != .Assume) then some p else none
  | _ => none

def headImpure (model : SemanticModel) (procNames : Std.HashSet String) (prelude : Std.HashSet String)
    (e : StmtExprMd) : Bool :=
  match e.val with
  | .StaticCall c _ _ => isProcCallee model procNames c || (preludePre? model prelude c).isSome
  | .New .. | .Var (.Field ..) | .Var (.Declare ..) | .IsType .. | .AsType .. | .Assign .. | .IncrDecr ..
  | .CompoundAssign .. | .Block .. | .Hole .. | .InstanceCall .. | .Throw .. | .Return ..
  | .Goto .. | .While .. | .Try .. | .Assert .. | .Assume .. => true
  | _ => false

def isImpure (e : StmtExprMd) : CM Bool := do
  let model := (← getThe TranslateState).model
  let procNames := (← get).procNames
  return anyStmtExpr (headImpure model procNames (← get).prelude) e

def isImpureIgnoringPreconditions (e : StmtExprMd) : CM Bool := do
  let model := (← getThe TranslateState).model
  let procNames := (← get).procNames
  return anyStmtExpr (headImpure model procNames {}) e

def isLiteral (e : StmtExprMd) : Bool :=
  match e.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv .. => true
  | _ => false

def isAtom (e : StmtExprMd) : Bool :=
  match e.val with
  | .Var (.Local _) | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .LiteralBv .. => true
  | _ => false

partial def wrapperBody (b : StmtExprMd) : Option StmtExprMd :=
  match b.val with
  | .Return [e] => some e
  | .Block [s] _ _ _ => wrapperBody s
  | .Block .. | .Return _ | .Assign .. | .IfThenElse _ _ none | .While .. => none
  | _ => some b

def substParams (σ : List (Nat × StmtExprMd)) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Var (.Local i) => match i.uniqueId with
      | some id => (σ.lookup id).getD n
      | none => n
    | _ => n) e

partial def inlineWrappers (model : SemanticModel) (prelude : Std.HashSet String)
    (e : StmtExprMd) (fuel : Nat := 16) : StmtExprMd :=
  if fuel == 0 then e else
  mapStmtExpr (fun n => match n.val with
    | .StaticCall callee args _ =>
      match model.get? callee with
      | some (.staticProcedure p) =>
        if !prelude.contains p.name.text then n else
        let body? := match p.body with
          | .Transparent b => wrapperBody b
          | .Opaque _ (some b) _ => wrapperBody b
          | _ => none
        match body? with
        | some b =>
          let σ := (p.inputs.zip args).filterMap fun (prm, a) => prm.name.uniqueId.map (·, a)
          let b' : StmtExprMd := { substParams σ b with source := n.source }
          inlineWrappers model prelude b' (fuel - 1)
        | none => n
      | _ => n
    | _ => n) e

def uncheckedIntOp : String → Option String
  | "Int.SafeDiv" => some "Int.Div"
  | "Int.SafeMod" => some "Int.Mod"
  | "Int.SafeDivT" => some "Int.DivT"
  | "Int.SafeModT" => some "Int.ModT"
  | _ => none

def pureExpr (e : StmtExprMd) : CM Expr := do
  let model := (← getThe TranslateState).model
  translateExpr (inlineWrappers model (← get).prelude e)

def uncheckedExpr (e : StmtExprMd) : CM Expr := do
  let r ← pureExpr e
  if !(← get).uncheck then return r
  return Cortex.mapExpr (fun
    | .op m o ty => (uncheckedIntOp o.name).map fun n => .op m ⟨n, o.metadata⟩ ty
    | _ => none) r

def typeOf (e : StmtExprMd) : CM HighTypeMd := do
  return computeExprType (← getThe TranslateState).model e

def fieldRefOf (fieldName : Identifier) : CM Cortex.FieldRef := do
  match (← getThe TranslateState).model.get? fieldName with
  | some (.field t _) => return { owner := t.text, field := fieldName.text }
  | _ => return { owner := "", field := fieldName.text }

def compositeNameOf (t : HighTypeMd) : Option String :=
  match t.val with
  | .UserDefined n => some n.text
  | _ => none

def outTemps (outs : List Parameter) (src : FileRange) : CM (List Identifier) :=
  outs.mapM fun o => freshTemp o.type src

def resolveOperator (name : String) (ty : HighTypeMd) (src : FileRange) : CM Identifier := do
  let model := (← getThe TranslateState).model
  let want := baseHigh model ty
  match (← get).preludeProcs.find? fun p =>
      p.name.text == name && p.inputs.head?.any fun i => highEq (baseHigh model i.type) want with
  | some p => return p.name
  | none => return ⟨name, none, src⟩

mutual

partial def purify (e : StmtExprMd) : CM StmtExprMd := do
  unless ← isImpure e do return e
  if let .Quantifier .. := e.val then
    unless ← isImpureIgnoringPreconditions e do return e
  let md := astNodeToCoreMd e
  let src := e.source
  match e.val with
  | .StaticCall callee args tyArgs =>
    let model := (← getThe TranslateState).model
    if isProcCallee model (← get).procNames callee then
      let args' ← purifyArgs args
      let (name, outs) ← calleeInfo callee
      let temps ← outTemps outs src
      emit (.call (idents (temps.map (·.text))) name (← args'.mapM pureExpr) md)
      match temps with
      | [t] => return varNode t src
      | _ =>
        unsupported src "a procedure call with other than one output in expression position"
        return e
    else if callee.text == "$andThen" || callee.text == "$orElse" || callee.text == "$implies" then
      match args with
      | [a, b] =>
        let a' ← purify a
        let r ← freshTemp ⟨.TBool, src⟩ src
        let rhs ← freshLabel "$sc_rhs"
        let short ← freshLabel "$sc_short"
        let join ← freshLabel "$sc_join"
        let ca ← pureExpr a'
        if callee.text == "$orElse" then
          sealWith (.condGoto ca short rhs md) short
          emit (.cmd (.set ⟨r.text, ()⟩ (.det Cortex.tt) md))
        else if callee.text == "$andThen" then
          sealWith (.condGoto ca rhs short md) short
          emit (.cmd (.set ⟨r.text, ()⟩ (.det Cortex.ff) md))
        else
          sealWith (.condGoto ca rhs short md) short
          emit (.cmd (.set ⟨r.text, ()⟩ (.det Cortex.tt) md))
        jumpTo join
        switchTo rhs
        let cb ← expr b
        emit (.cmd (.set ⟨r.text, ()⟩ (.det cb) md))
        fallInto join
        return varNode r src
      | _ => return e
    else
      let args' ← purifyArgs args
      if let some p := preludePre? model (← get).prelude callee then
        let σ := (p.inputs.zip args').filterMap fun (prm, a) => prm.name.uniqueId.map (·, a)
        let mut conds : Array Expr := #[]
        for c in p.preconditions do
          if c.mode == .Assume then continue
          let cond ← pureExpr { substParams σ c.condition with source := src }
          let md' := match c.summary with
            | some msg => md.pushElem Imperative.MetaData.propertySummary (.msg msg)
            | none => md.pushElem Imperative.MetaData.propertySummary (.msg "precondition")
          emit (.cmd (.assert s!"pre_{(← get).fresh}" cond md'))
          modify fun s => { s with fresh := s.fresh + 1 }
          conds := conds.push cond
        let node : StmtExprMd := { e with val := .StaticCall callee args' tyArgs }
        let tmp ← freshTemp (← typeOf e) src
        let rhs ← uncheckedExpr node
        if (← get).uncheck || conds.isEmpty then
          emit (.cmd (.set ⟨tmp.text, ()⟩ (.det rhs) md))
        else
          let unmet ← freshLabel "$pre_unmet"
          let join ← freshLabel "$pre_join"
          for cond in conds do
            let ok ← freshLabel "$pre_ok"
            sealWith (.condGoto cond ok unmet md) ok
          emit (.cmd (.set ⟨tmp.text, ()⟩ (.det rhs) md))
          jumpTo join
          switchTo unmet
          emit (.cmd (.set ⟨tmp.text, ()⟩ .nondet md))
          fallInto join
        return varNode tmp src
      return { e with val := .StaticCall callee args' tyArgs }
  | .ReferenceEquals a b =>
    match ← purifyArgs [a, b] with
    | [a', b'] => return { e with val := .ReferenceEquals a' b' }
    | _ => return e
  | .IfThenElse c t (some f) =>
    let c' ← purify c
    let r ← freshTemp (← typeOf e) src
    let lt ← freshLabel "$ite_then"
    let lf ← freshLabel "$ite_else"
    let join ← freshLabel "$ite_join"
    sealWith (.condGoto (← pureExpr c') lt lf md) lt
    let vt ← expr t
    emit (.cmd (.set ⟨r.text, ()⟩ (.det vt) md))
    jumpTo join
    switchTo lf
    let vf ← expr f
    emit (.cmd (.set ⟨r.text, ()⟩ (.det vf) md))
    fallInto join
    return varNode r src
  | .Var (.Field target fieldName) =>
    let o ← expr target
    let ref ← fieldRefOf fieldName
    let r ← freshTemp (← typeOf e) src
    emit (.readField ⟨r.text, ()⟩ o ref md)
    return varNode r src
  | .New ref tyArgs =>
    unless tyArgs.isEmpty do unsupported src "generic composite allocation"
    let r ← freshTemp ⟨.UserDefined ref, src⟩ src
    emit (.new ⟨r.text, ()⟩ ref.text md)
    return varNode r src
  | .IsType target ty =>
    let o ← expr target
    let r ← freshTemp ⟨.TBool, src⟩ src
    match compositeNameOf ty with
    | some n => emit (.instanceOf ⟨r.text, ()⟩ o n md)
    | none => unsupported src "a type test against a non-composite type"
    return varNode r src
  | .AsType target ty =>
    let t' ← purify target
    let t' ← if isAtom t' then pure t' else do
      let tmp ← freshTemp (← typeOf target) src
      emit (.cmd (.set ⟨tmp.text, ()⟩ (.det (← pureExpr t')) md))
      pure (varNode tmp src)
    match compositeNameOf ty with
    | some n =>
      let b ← freshTemp ⟨.TBool, src⟩ src
      emit (.instanceOf ⟨b.text, ()⟩ (← pureExpr t') n md)
      emit (.cmd (.assert "cast" (mkFvar b.text) md))
    | none => unsupported src "a cast to a non-composite type"
    return t'
  | .Block ss _ _ _ =>
    match ss.reverse with
    | [] => return e
    | last :: rest =>
      for s in rest.reverse do stmt s
      purify last
  | .Assign targets _ =>
    stmt e
    match targets with
    | [t] =>
      match t.val with
      | .Local i => return varNode i src
      | .Declare p => return varNode p.name src
      | .Field o f => return { e with val := .Var (.Field o f) } |> fun n => n
    | _ =>
      unsupported src "a multi-target assignment in expression position"
      return e
  | .IncrDecr mode op target =>
    let old ← freshTemp (← typeOf e) src
    let cur ← readVar target
    emit (.cmd (.set ⟨old.text, ()⟩ (.det cur) md))
    let newV := incrDecrExpr op (mkFvar old.text)
    writeVar target newV md
    match mode with
    | .Post => return varNode old src
    | .Pre =>
      let n ← freshTemp (← typeOf e) src
      emit (.cmd (.set ⟨n.text, ()⟩ (.det newV) md))
      return varNode n src
  | .CompoundAssign op target rhs =>
    let cur ← readVar target
    let curT ← freshTemp (← typeOf e) src
    emit (.cmd (.set ⟨curT.text, ()⟩ (.det cur) md))
    let rhs' ← purify rhs
    let tv : Identifier := curT
    let callee ← resolveOperator op.procName (← typeOf e) src
    let node : StmtExprMd := { e with val := .StaticCall callee [varNode tv src, rhs'] [] }
    let newV ← expr node
    let n ← freshTemp (← typeOf e) src
    emit (.cmd (.set ⟨n.text, ()⟩ (.det newV) md))
    writeVar target (mkFvar n.text) md
    return varNode n src
  | .Hole _ ty =>
    let ty' := ty.getD (← typeOf e)
    let r ← freshTemp ty' src
    emit (.cmd (.set ⟨r.text, ()⟩ .nondet md))
    return varNode r src
  | .InstanceCall target callee args =>
    match ← virtualCallOf target callee args md src (some e) with
    | [t] => return varNode t src
    | _ =>
      unsupported src "an instance call with other than one output in expression position"
      return e
  | _ =>
    unsupported src "this construct in expression position"
    return e

partial def purifyArgs (args : List StmtExprMd) : CM (List StmtExprMd) := do
  let flags ← args.mapM isImpure
  let lastImpure := (flags.zipIdx.filter (·.1)).map (·.2) |>.getLast?
  match lastImpure with
  | none => return args
  | some k =>
    let mut out := #[]
    for (a, i) in args.zipIdx do
      let a' ← purify a
      if i < k && !isLiteral a' then
        let tmp ← freshTemp (← typeOf a) a.source
        emit (.cmd (.set ⟨tmp.text, ()⟩ (.det (← pureExpr a')) (astNodeToCoreMd a)))
        out := out.push (varNode tmp a.source)
      else
        out := out.push a'
    return out.toList

partial def expr (e : StmtExprMd) : CM Expr := do
  pureExpr (← purify e)

partial def readVar (v : AstNode Variable) : CM Expr := do
  match v.val with
  | .Local i => pureExpr (varNode i v.source)
  | .Field o f => expr { val := .Var (.Field o f), source := v.source }
  | .Declare p => return mkFvar p.name.text

partial def writeVar (v : AstNode Variable) (val : Expr) (md : MD) : CM Unit := do
  match v.val with
  | .Local i => emit (.cmd (.set ⟨i.text, ()⟩ (.det val) md))
  | .Declare p =>
    declLocal p.name.text (← lty (p.type.getD ⟨.Unknown, v.source⟩))
    emit (.cmd (.set ⟨p.name.text, ()⟩ (.det val) md))
  | .Field o f =>
    let o' ← expr o
    emit (.writeField o' (← fieldRefOf f) val md)

partial def incrDecrExpr (op : IncrDecrOp) (x : Expr) : Expr :=
  match op with
  | .Incr => Cortex.mkApp Core.intAddOp [x, Cortex.intLit 1]
  | .Decr => Cortex.mkApp Core.intSubOp [x, Cortex.intLit 1]

partial def virtualCallOf (target : StmtExprMd) (callee : Identifier) (args : List StmtExprMd)
    (md : MD) (src : FileRange) (_whole : Option StmtExprMd) : CM (List Identifier) := do
  let recv ← purify target
  let recv ← if isAtom recv then pure recv else do
    let tmp ← freshTemp (← typeOf target) src
    emit (.cmd (.set ⟨tmp.text, ()⟩ (.det (← pureExpr recv)) md))
    pure (varNode tmp src)
  let args' ← purifyArgs args
  let argEs ← (recv :: args').mapM pureExpr
  match (← getThe TranslateState).model.get? callee with
  | some (.instanceProcedure owner p) =>
    let temps ← outTemps p.outputs src
    let lhs := temps.map (·.text)
    emit (.virtualCall (idents lhs) owner.text p.name.text argEs md)
    return temps
  | _ =>
    unsupported src "an instance call that does not resolve to an instance procedure"
    return []

partial def callStmt (callee : Identifier) (args : List StmtExprMd) (lhs : Option (List String))
    (md : MD) (src : FileRange) : CM Unit := do
  let args' ← purifyArgs args
  let (name, outs) ← calleeInfo callee
  let lhs ← match lhs with
    | some l => pure l
    | none => (·.map (·.text)) <$> outTemps outs src
  emit (.call (idents lhs) name (← args'.mapM pureExpr) md)

partial def runFinals (stop : Nat) : CM Unit := do
  let s ← get
  let saved := s.finals
  let savedRegion := s.cur.region
  let rec go : List Final → Nat → CM Unit
    | [], _ => pure ()
    | f :: rest, n =>
      if n ≤ stop then pure () else do
        modify fun s => { s with finals := rest }
        setRegion f.outer
        stmt f.body
        go rest (n - 1)
  go saved saved.length
  modify fun s => { s with finals := saved }
  setRegion savedRegion

partial def stmt (e : StmtExprMd) : CM Unit := do
  let md := astNodeToCoreMd e
  let src := e.source
  match e.val with
  | .Block ss label invs dec =>
    unless invs.isEmpty do unsupported src "block invariants"
    unless dec.isNone do unsupported src "termination measures"
    match label with
    | none => for s in ss do stmt s
    | some l =>
      let start ← freshLabel s!"{l}$start"
      let stop ← freshLabel s!"{l}$end"
      fallInto start
      let depth := (← get).finals.length
      modify fun s => { s with frames := { name := l, start, stop, finDepth := depth } :: s.frames }
      for s in ss do stmt s
      modify fun s => { s with frames := s.frames.drop 1 }
      fallInto stop
  | .Goto target dest =>
    match (← get).frames.find? (·.name == target) with
    | none => unsupported src s!"a goto to the unknown label '{target}'"
    | some f =>
      runFinals f.finDepth
      match dest with
      | .blockStart => jumpTo f.start
      | .blockEnd => jumpTo f.stop
  | .IfThenElse c t f =>
    let c' ← expr c
    let lt ← freshLabel "$then"
    let lf ← freshLabel "$else"
    let join ← freshLabel "$endif"
    sealWith (.condGoto c' lt lf md) lt
    stmt t
    jumpTo join
    switchTo lf
    if let some f := f then stmt f
    fallInto join
  | .While c invs dec body postTest =>
    unless invs.isEmpty do unsupported src "loop invariants"
    unless dec.isNone do unsupported src "termination measures"
    let head ← freshLabel "$loop_head"
    let bodyL ← freshLabel "$loop_body"
    let exit ← freshLabel "$loop_exit"
    if postTest then
      fallInto bodyL
      stmt body
      fallInto head
      let c' ← expr c
      sealWith (.condGoto c' bodyL exit md) exit
    else
      fallInto head
      let c' ← expr c
      sealWith (.condGoto c' bodyL exit md) bodyL
      stmt body
      jumpTo head
      switchTo exit
  | .Return vals =>
    let outs := (← get).outputs
    if vals.length != outs.length && !vals.isEmpty then
      unsupported src "a return whose value count differs from the output count"
    let es ← vals.mapM expr
    let temps ← if es.length > 1 then
        (vals.zip es).mapM fun (v, ev) => do
          let t ← freshTemp (← typeOf v) src
          emit (.cmd (.set ⟨t.text, ()⟩ (.det ev) md))
          pure (mkFvar t.text)
      else pure es
    for (o, ev) in outs.zip temps do
      emit (.cmd (.set ⟨o, ()⟩ (.det ev) md))
    runFinals 0
    jumpTo (← get).retLabel
  | .Assign targets value =>
    match value.val with
    | .StaticCall callee args _ =>
      if isProcCallee (← getThe TranslateState).model (← get).procNames callee then
        assignCall targets md src fun lhs => callStmt callee args (some lhs) md src
      else assignValue targets value md src
    | .InstanceCall target callee args =>
      let temps ← virtualCallOf target callee args md src none
      for (t, tv) in targets.zip temps do
        writeVar t (mkFvar tv.text) md
    | _ => assignValue targets value md src
  | .Var (.Declare p) =>
    declLocal p.name.text (← lty (p.type.getD ⟨.Unknown, src⟩))
    emit (.cmd (.set ⟨p.name.text, ()⟩ .nondet md))
  | .StaticCall callee args _ =>
    if isProcCallee (← getThe TranslateState).model (← get).procNames callee then
      callStmt callee args none md src
    else
      let _ ← purify e
  | .InstanceCall target callee args =>
    let _ ← virtualCallOf target callee args md src none
  | .Throw v =>
    let ty ← typeOf v
    let v' ← expr v
    let md ← match compositeNameOf ty with
      | some n => pure (md.pushElem Imperative.MetaData.propertySummary (.msg s!"uncaught exception '{n}' is not thrown"))
      | none =>
        unsupported v.source "a non-composite thrown value"
        pure md
    emit (.throw v' md)
    deadEnd
  | .Assert c summary =>
    let c' ← expr c
    let md' := match summary with
      | some msg => md.pushElem Imperative.MetaData.propertySummary (.msg msg)
      | none => md
    emit (.cmd (.assert s!"assert_{(← get).fresh}" c' md'))
    modify fun s => { s with fresh := s.fresh + 1 }
  | .Assume c =>
    let c' ← expr c
    emit (.cmd (.assume s!"assume_{(← get).fresh}" c' md))
    modify fun s => { s with fresh := s.fresh + 1 }
  | .Try body catches finally? => tryStmt body catches finally? md src
  | .IncrDecr .. | .CompoundAssign .. =>
    let _ ← purify e
  | _ =>
    if ← isImpure e then
      let _ ← purify e
    else pure ()

partial def assignCall (targets : List (AstNode Variable)) (md : MD) (src : FileRange)
    (k : List String → CM Unit) : CM Unit := do
  let direct := targets.all fun t => match t.val with
    | .Local _ | .Declare _ => true
    | _ => false
  if direct then
    let names ← targets.mapM fun t => match t.val with
      | .Local i => pure i.text
      | .Declare p => do
        declLocal p.name.text (← lty (p.type.getD ⟨.Unknown, src⟩))
        pure p.name.text
      | .Field _ f => pure f.text
    k names
  else
    let temps ← targets.mapM fun t => do
      let ty ← match t.val with
        | .Field o f => typeOf { val := .Var (.Field o f), source := t.source }
        | .Local i => typeOf (varNode i t.source)
        | .Declare p => pure (p.type.getD ⟨.Unknown, src⟩)
      freshTemp ty src
    k (temps.map (·.text))
    for (t, tv) in targets.zip temps do
      writeVar t (mkFvar tv.text) md

partial def assignValue (targets : List (AstNode Variable)) (value : StmtExprMd) (md : MD)
    (src : FileRange) : CM Unit := do
  match targets with
  | [t] =>
    match t.val with
    | .Field o f =>
      let o' ← purify o
      let o' ← if isAtom o' then pure o' else do
        let tmp ← freshTemp (← typeOf o) src
        emit (.cmd (.set ⟨tmp.text, ()⟩ (.det (← pureExpr o')) md))
        pure (varNode tmp src)
      let v ← expr value
      emit (.writeField (← pureExpr o') (← fieldRefOf f) v md)
    | _ =>
      let v ← expr value
      writeVar t v md
  | _ => unsupported src "a multi-target assignment of a non-call value"

partial def tryStmt (body : StmtExprMd) (catches : List CatchClause) (finally? : Option StmtExprMd)
    (md : MD) (src : FileRange) : CM Unit := do
  let outer := (← get).cur.region
  let hid := (← get).handlers.size
  let finId := hid + 1
  let anyExn : HighTypeMd := ⟨.UserDefined ⟨"$AnyComposite", none, src⟩, src⟩
  let excVar ← freshTemp anyExn src
  let dispatch ← freshLabel "$catch_dispatch"
  modify fun s => { s with handlers := s.handlers.push { id := hid, binder := excVar.text, target := dispatch } }
  let fexcVar ← freshTemp anyExn src
  let finHandler ← freshLabel "$finally_exn"
  let afterTry ← freshLabel "$try_end"
  let catchRegion := if finally?.isSome then some finId else outer
  if finally?.isSome then
    modify fun s => { s with handlers := s.handlers.push { id := finId, binder := fexcVar.text, target := finHandler } }
  if let some f := finally? then
    modify fun s => { s with finals := { body := f, outer := outer } :: s.finals }
  setRegion (some hid)
  stmt body
  setRegion catchRegion
  jumpTo afterTry
  switchTo dispatch
  for c in catches do
    declLocal c.binding.text (← lty c.bindingType)
    emit (.cmd (.set ⟨c.binding.text, ()⟩ (.det (mkFvar excVar.text)) md))
    match c.predicate with
    | none =>
      stmt c.body
      jumpTo afterTry
    | some p =>
      let pv ← expr p
      let yes ← freshLabel "$catch"
      let no ← freshLabel "$catch_next"
      sealWith (.condGoto pv yes no md) yes
      stmt c.body
      jumpTo afterTry
      switchTo no
  emit (.throw (mkFvar excVar.text) md)
  deadEnd
  if let some f := finally? then
    modify fun s => { s with finals := s.finals.drop 1 }
    switchTo finHandler
    modify fun s => { s with cur := { s.cur with region := outer } }
    stmt f
    emit (.throw (mkFvar fexcVar.text) md)
    deadEnd
    switchTo afterTry
    modify fun s => { s with cur := { s.cur with region := outer } }
    stmt f
  else
    switchTo afterTry
    modify fun s => { s with cur := { s.cur with region := outer } }

end

def reachableLabels (entry : String) (blocks : Array (String × LBlock × Option Nat))
    (handlers : Array HInfo) : Std.HashSet String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut work := [entry]
  let mut fuel := blocks.size * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | l :: rest =>
      work := rest
      if seen.contains l then continue
      seen := seen.insert l
      match blocks.find? (·.1 == l) with
      | none => pure ()
      | some (_, blk, region) =>
        let succs := match blk.transfer with
          | .condGoto _ lt lf _ => [lt, lf]
          | .finish _ => []
        let hsuccs := match region with
          | some r => (handlers.filter (·.id == r)).toList.map (·.target)
          | none => []
        work := succs ++ hsuccs ++ work
  return seen

def declaredIds (e : StmtExprMd) : List Identifier :=
  foldStmtExpr (fun n acc => match n.val with
    | .Var (.Declare p) => p.name :: acc
    | .Assign targets _ => targets.filterMap (fun t => match t.val with
        | .Declare p => some p.name
        | _ => none) ++ acc
    | .Try _ cs _ => cs.map (·.binding) ++ acc
    | _ => acc) [] e

def shadowRenames (params : List Identifier) (body : StmtExprMd) : Std.HashMap Nat String := Id.run do
  let mut owner : Std.HashMap String (Option Nat) := {}
  for p in params do owner := owner.insert p.text p.uniqueId
  let mut renames : Std.HashMap Nat String := {}
  for d in (declaredIds body).reverse do
    match owner.get? d.text, d.uniqueId with
    | none, _ => owner := owner.insert d.text d.uniqueId
    | some o, some u => if o != some u then renames := renames.insert u s!"{d.text}${u}"
    | some _, none => pure ()
  return renames

def renameId (r : Std.HashMap Nat String) (i : Identifier) : Identifier :=
  match i.uniqueId.bind r.get? with
  | some t => { i with text := t }
  | none => i

def renameVar (r : Std.HashMap Nat String) (v : AstNode Variable) : AstNode Variable :=
  match v.val with
  | .Local i => { v with val := .Local (renameId r i) }
  | .Declare p => { v with val := .Declare { p with name := renameId r p.name } }
  | .Field .. => v

def renameShadowed (params : List Identifier) (body : StmtExprMd) : StmtExprMd :=
  let r := shadowRenames params body
  if r.isEmpty then body else
  mapStmtExpr (fun n => match n.val with
    | .Var v => { n with val := .Var (renameVar r ⟨v, n.source⟩).val }
    | .Assign ts v => { n with val := .Assign (ts.map (renameVar r)) v }
    | .IncrDecr m o t => { n with val := .IncrDecr m o (renameVar r t) }
    | .CompoundAssign o t v => { n with val := .CompoundAssign o (renameVar r t) v }
    | .Try b cs f => { n with val := .Try b (cs.map fun c => { c with binding := renameId r c.binding }) f }
    | _ => n) body

def translateBody (proc : Strata.Laurel.Procedure) (body : StmtExprMd) : CM Cortex.Body := do
  modify fun s => { s with
    sealed := #[], cur := { label := "$start" }, frames := [], finals := [], handlers := #[],
    locals := #[], outputs := proc.outputs.map (·.name.text) }
  stmt (renameShadowed ((proc.inputs ++ proc.outputs).map (·.name)) body)
  jumpTo "$return"
  switchTo "$return"
  sealWith (.finish .empty) "$unused"
  let s ← get
  let inits : List IRCmd := s.locals.toList.filterMap fun (x, ty) =>
    if proc.inputs.any (·.name.text == x) || proc.outputs.any (·.name.text == x) then none
    else some (.cmd (.init ⟨x, ()⟩ ty .nondet .empty))
  let entryBlk : LBlock := { cmds := inits, transfer := .goto "$start" }
  let all := #[("$entry", entryBlk, (none : Option Nat))] ++ s.sealed
  let live := reachableLabels "$entry" all s.handlers
  let all := all.filter fun (l, _, _) => live.contains l
  let handlers : Cortex.ExnTable := s.handlers.toList.filterMap fun h =>
    let covered := (all.filter fun (_, _, r) => r == some h.id).toList.map (·.1)
    if covered.isEmpty then none
    else some { covered, catchType := none, binder := ⟨h.binder, ()⟩, target := h.target, md := .empty }
  return { cfg := { entry := "$entry", blocks := all.toList.map fun (l, b, _) => (l, b) }, handlers }

def translateParams (ps : List Parameter) : CM (List (Core.Expression.Ident × LTy)) :=
  ps.mapM fun p => do return (⟨p.name.text, ()⟩, ← lty p.type)

def hasContract (proc : Strata.Laurel.Procedure) : Bool :=
  proc.preconditions.any (·.mode != .Assume) ||
  match proc.body with
  | .Opaque posts _ _ | .Abstract posts => posts.any (·.mode != .Assume)
  | _ => false

def frameUnbounded (model : SemanticModel) (p : Strata.Laurel.Procedure) : Bool :=
  p.name.uniqueId.any model.heapWriters.contains &&
  match p.body with
  | .Opaque _ _ gs => gs.any (!·.targets.isEmpty) || p.throwsOn.any (!·.modifies.isEmpty)
  | _ => true

def writesUnframed (model : SemanticModel) (cs : List CompositeType) (e : StmtExprMd) : Bool :=
  match e.val with
  | .Assign ts _ => ts.any fun t => (t.val matches .Field ..)
  | .IncrDecr _ _ t => (t.val matches .Field ..)
  | .CompoundAssign _ t _ => (t.val matches .Field ..)
  | .StaticCall c _ _ => match model.get? c with
    | some (.staticProcedure p) => frameUnbounded model p
    | _ => false
  | .InstanceCall _ c _ => match model.get? c with
    | some (.instanceProcedure _ p) => cs.any fun comp =>
      comp.instanceProcedures.any fun q => q.name.text == p.name.text && frameUnbounded model q
    | _ => true
  | _ => false

def hasFrame (model : SemanticModel) (cs : List CompositeType) (proc : Strata.Laurel.Procedure) : Bool :=
  proc.throwsOn.any (fun b => !b.modifies.isEmpty && !hasModifiesWildcard b.modifies) ||
  match proc.body with
  | .Opaque _ impl gs =>
    gs.any (fun g => !g.targets.isEmpty && !hasModifiesWildcard g.targets) ||
    (!gs.any (fun g => g.guard.isNone && hasModifiesWildcard g.targets) &&
      impl.any (anyStmtExpr (writesUnframed model cs)))
  | _ => false

def translateProcedure (cortexName : String) (proc : Strata.Laurel.Procedure) : CM Cortex.Procedure := do
  let impl := match proc.body with
    | .Transparent b => some b
    | .Opaque _ impl _ => impl
    | _ => none
  if hasContract proc then
    unsupported proc.name.source s!"the contract of procedure '{proc.name.text}'"
  if hasFrame (← getThe TranslateState).model (← get).composites proc then
    unsupported proc.name.source s!"the frame of procedure '{proc.name.text}'"
  let throws ← match proc.throwsType with
    | none => pure none
    | some t => match compositeNameOf t with
      | some n => pure (some n)
      | none =>
        unsupported t.source "a non-composite throws type"
        pure none
  let inputs ← translateParams proc.inputs
  let outputs ← translateParams proc.outputs
  let body ← impl.mapM (translateBody proc)
  let md := identifierToCoreMd proc.name
  let md := if proc.isInterpretEntry then md.pushElem Imperative.MetaData.interpretEntry (.switch true) else md
  return { name := cortexName, inputs, outputs, throws, body, md }

def translateComposite (c : CompositeType) : CM Cortex.CompositeDecl := do
  unless c.typeArgs.isEmpty do unsupported c.name.source "generic composite types"
  let fields ← c.fields.mapM fun f => do return ({ name := f.name.text, ty := ← lty f.type } : Cortex.FieldDecl)
  return { name := c.name.text, extending := c.extending.filterMap compositeNameOf, fields }

def translateConstrained (c : ConstrainedType) : CM Cortex.ConstrainedDecl := do
  let constraint ← if ← isImpureIgnoringPreconditions c.constraint then do
      unsupported c.constraint.source s!"a constraint of '{c.name.text}' that reads the heap, calls a procedure or tests a type"
      pure Cortex.tt
    else pureExpr c.constraint
  let witness ← if ← isImpure c.witness then pure none else some <$> pureExpr c.witness
  return { name := c.name.text, base := ← lty c.base, binder := ⟨c.valueName.text, ()⟩, constraint, witness }

def translateProgram (prelude : Std.HashSet String) (program : LaurelProgram) : CM Cortex.Module := do
  unless program.staticFields.isEmpty do unsupported .unknown "static fields"
  unless program.staticFunctions.isEmpty do unsupported .unknown "static functions"
  unless program.constants.isEmpty do unsupported .unknown "constants"
  let composites := program.types.filterMap fun | .Composite c => some c | _ => none
  let userProcs := program.staticProcedures.filter fun p => !prelude.contains p.name.text
  let procNames : Std.HashSet String := userProcs.foldl (fun s p => s.insert p.name.text) {}
  let preludeProcs := program.staticProcedures.filter fun p => prelude.contains p.name.text
  modify fun s => { s with composites, procNames, prelude, preludeProcs }
  let mut decls : Array Core.Decl := #[]
  let mut cdecls := #[]
  let mut constrained := #[]
  for t in program.types do
    match t with
    | .Composite c => cdecls := cdecls.push (← translateComposite c)
    | .Constrained c => constrained := constrained.push (← translateConstrained c)
    | .Datatype dt =>
      let ldt ← translateDatatypeDefinition dt
      decls := decls.push (.type (.data [ldt]) .empty)
    | .Opaque ot =>
      if Core.KnownTypes.keywords.contains ot.name.text then continue
      decls := decls.push (.type (.con { name := ot.name.text, params := ot.typeArgs.map (·.text) }) .empty)
    | .Alias _ => pure ()
  let mut procs := #[]
  for p in userProcs do
    procs := procs.push (← translateProcedure p.name.text p)
  for c in composites do
    for p in c.instanceProcedures do
      procs := procs.push (← translateProcedure s!"{c.name.text}${p.name.text}" p)
  return { program := { composites := cdecls.toList, constrained := constrained.toList,
                        procedures := procs.toList },
           decls := decls.toList }

def run (model : SemanticModel) (program : LaurelProgram) (overflowChecks : Core.OverflowChecks := {})
    (uncheck : Bool := true) : Option Cortex.Module × List Message :=
  let prelude : Std.HashSet String :=
    coreDefinitionsForLaurel.staticProcedures.foldl (fun s p => s.insert p.name.text) {}
  let initState : TranslateState := { model, overflowChecks }
  let st : CState := { cur := { label := "$start" }, uncheck }
  let (res, ts) := runTranslateM initState ((translateProgram prelude program).run' st)
  let diags := ts.diagnostics.reverse
  match res with
  | .error msg => (none, diags ++ [Message.fromString s!"Cortex translation failed: {msg}" MessageKind.strataBug])
  | .ok m => if diags.any (·.kind != .warning) then (none, diags) else (some m, diags)

end

end Cortex.FromLaurel
