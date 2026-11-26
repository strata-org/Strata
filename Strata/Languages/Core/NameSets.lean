/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.Program
public import Strata.Util.Name

/-! # The names a generated name avoids

A pass that generates a name picks it fresh against the names of the program it receives, so the
set holds what earlier passes generated too. Which set depends on what the pass generates:

- `Program.declaredNames`: a declaration (an opaque type, a closed lemma's type). The names of
  the declarations, the types procedure bodies declare, and the datatypes' type parameters.
- `Program.takenNames`: a lemma (termination checking, precondition elimination). The names of
  `Program.declaredNames` and the labels of every procedure's checks, which name proof obligations
  too. Precondition elimination also inserts checks into procedure bodies; it renames them after
  the pass, apart from the declaration names and the other labels of their own procedure.
- `Program.internalNames`: every name in the `$__` namespace reserved for generated names, whose
  prefixes a program records (`Program.usedIdentPrefixes`), so that a pass can tell from the
  record alone that no name starts with its own prefix.
- `Program.varNames`: a variable (call elimination's temporaries). Every procedure's parameters
  and the variables its body initializes. It holds no declaration names; call elimination adds
  them as a precaution. Bound variables need no entry, since expressions refer to them by de
  Bruijn index and a substitution cannot capture them.
-/

public section

namespace Core

/-- Replace the label and the metadata of each `assert`, `assume` and `cover` of
    a procedure body by what `f` returns for them, at every depth of a
    structured body and in every block of a CFG body, in order. -/
def Procedure.Body.mapCheckLabelsM {M : Type → Type} [Monad M]
    (f : String → Imperative.MetaData Expression → M (String × Imperative.MetaData Expression))
    (body : Procedure.Body) : M Procedure.Body := do
  let g : Command → M Command := fun
    | .cmd (.assert l e md) => do let (l, md) ← f l md; return .cmd (.assert l e md)
    | .cmd (.assume l e md) => do let (l, md) ← f l md; return .cmd (.assume l e md)
    | .cmd (.cover l e md) => do let (l, md) ← f l md; return .cmd (.cover l e md)
    | c => pure c
  match body with
  | .structured ss o => return .structured (← Imperative.Block.mapExprM pure g ss) o
  | .cfg g' o =>
    return .cfg { g' with blocks := ← g'.blocks.mapM fun (l, b) =>
      return (l, { b with cmds := ← b.cmds.mapM g }) } o
  | .abstract => return .abstract

/-- The labels of a procedure's checks: its contract's `requires` and `ensures`
    clauses, which the procedure check turns into an `assume` and an `assert`
    under the same label; its body's `assert`, `assume` and `cover` commands
    (`Procedure.Body.mapCheckLabelsM`); and the loop invariants of a structured
    body. CFG blocks carry no labelled loop invariants, and a block's transfer
    carries no label. -/
def Decl.checkLabels : Decl → List String
  | .proc q _ =>
    let record (l : String) (md : Imperative.MetaData Expression) :
        StateM (List String) (String × Imperative.MetaData Expression) :=
      modifyGet fun ls => ((l, md), l :: ls)
    let (_, bodyLabels) := (Procedure.Body.mapCheckLabelsM record q.body).run []
    let invariantLabels := match q.body with
      | .structured ss _ => (Statements.collectAssertIds ss).map (·.label)
      | .cfg _ _ | .abstract => []
    q.spec.preconditions.map (·.1) ++ q.spec.postconditions.map (·.1) ++
      bodyLabels.reverse ++ invariantLabels
  | _ => []

/-- The type parameters of the program's datatypes. The SMT encoder declares a datatype with
    its parameters bound by name (`par`), so a sort a pass generates must not reuse one. -/
def Program.dataTypeParams (p : Program) : List String :=
  p.decls.flatMap fun
    | .type (.data block) _ => block.flatMap (·.typeArgs)
    | _ => []

/-- The names `p` declares: the names of its declarations, the types its procedure bodies
    declare, and its datatypes' type parameters. Types, functions, axioms, lemmas and procedures share one
    namespace of declaration names, so a pass that names a new declaration with a prefix
    avoids every one of these names with that prefix, not only the type names. -/
def Program.declaredNames (p : Program) : List String :=
  p.getNames.map (·.name) ++ (p.typeNames ++ p.dataTypeParams)

/-- The names of the variables a procedure declares: its input and output parameters, and the
    variables its body initializes, at any nesting depth of a structured body or in any block of
    a CFG body. A pass that adds variables to the procedure must avoid them. -/
def Procedure.varNames (p : Procedure) : List String :=
  let locals := match p.body with
    | .structured ss _ => Imperative.Block.definedVars ss false
    | .cfg g _ => g.blocks.flatMap fun (_, b) => b.cmds.flatMap Command.definedVars
    | .abstract => []
  (p.header.inputs.keys ++ p.header.outputs.keys ++ locals).map (·.name)

/-- The names of the variables the program's procedures declare (`Procedure.varNames`). -/
def Program.varNames (p : Program) : Std.HashSet String :=
  Std.HashSet.ofList <| p.decls.flatMap fun
    | .proc proc _ => proc.varNames
    | _ => []

/-- The names a generated lemma avoids: the names `p` declares (`Program.declaredNames`) and the
    labels of every procedure's checks in `p`. -/
def Program.takenNames (p : Program) : List String :=
  p.declaredNames ++ p.decls.flatMap Decl.checkLabels

/-! ## Names in the namespace reserved for generated names

Names starting with `$__` (`Strata.Name.internalMarker`) are reserved for the names Strata
generates. `Program.internalNames` lists every such name of a program, wherever it occurs, and
`Program.usedIdentPrefixes` records prefixes covering them (`Program.identPrefixesCovered`): the
type-checking phase collects them, and a pass that adds such names is to add their prefixes
(`Program.addIdentPrefixes`). When the record is `none`, the prefixes are collected on demand
(`Program.knownIdentPrefixes`). -/

namespace Program.InternalNames

open Imperative Lambda

/-- The names collected so far. -/
abbrev Acc := Array String

/-- Add `n` to `acc` when it is internal. -/
@[inline] def add (acc : Acc) (n : String) : Acc :=
  if Strata.Name.isInternal n then acc.push n else acc

/-- Add the internal names of `ns`. -/
def addAll (acc : Acc) (ns : List String) : Acc := ns.foldl add acc

mutual
/-- The internal names of a monotype: its type variables and type constructors. -/
def monoTy (acc : Acc) : LMonoTy → Acc
  | .ftvar n => add acc n
  | .tcons n args => monoTys (add acc n) args
  | .bitvec _ => acc
/-- `monoTy` for each type of a list. -/
def monoTys (acc : Acc) : List LMonoTy → Acc
  | [] => acc
  | t :: ts => monoTys (monoTy acc t) ts
end

/-- The internal names of a type scheme: its bound type variables and its body. -/
def ty (acc : Acc) : LTy → Acc
  | .forAll vs t => monoTy (addAll acc vs) t

/-- The internal names of an optional monotype annotation. -/
def optTy (acc : Acc) : Option LMonoTy → Acc
  | some t => monoTy acc t
  | none => acc

/-- The internal names of an expression: its operators, free variables and type annotations. The
    display names of binders are not names a program refers to, so they are not collected. -/
def expr (acc : Acc) : Expression.Expr → Acc
  | .const _ _ | .bvar _ _ => acc
  | .op _ o t => optTy (add acc o.name) t
  | .fvar _ x t => optTy (add acc x.name) t
  | .abs _ _ t e => expr (optTy acc t) e
  | .quant _ _ _ t tr e => expr (expr (optTy acc t) tr) e
  | .app _ f a => expr (expr acc f) a
  | .ite _ c t e => expr (expr (expr acc c) t) e
  | .eq _ a b => expr (expr acc a) b

/-- `expr` for each expression of a list. -/
def exprs (acc : Acc) (es : List Expression.Expr) : Acc := es.foldl expr acc

/-- The internal names of a right-hand side. -/
def exprOrNondet (acc : Acc) : ExprOrNondet Expression → Acc
  | .det e => expr acc e
  | .nondet => acc

/-- The internal names of a signature: its parameter names and types. -/
def signature (acc : Acc) (sig : List (CoreIdent × LMonoTy)) : Acc :=
  sig.foldl (fun acc (x, t) => monoTy (add acc x.name) t) acc

/-- The internal names of a command: the variables it declares, writes and reads, its label, the
    procedure it calls and the type arguments of the call. -/
def command (acc : Acc) : Command → Acc
  | .cmd (.init x t e _) => exprOrNondet (ty (add acc x.name) t) e
  | .cmd (.set x e _) => exprOrNondet (add acc x.name) e
  | .cmd (.assert l b _) | .cmd (.assume l b _) | .cmd (.cover l b _) => expr (add acc l) b
  | .call p tyArgs args _ =>
    let acc := (tyArgs.getD []).foldl ty (add acc p)
    args.foldl (init := acc) fun acc a => match a with
      | .inArg e => expr acc e
      | .inoutArg x | .outArg x => add acc x.name

/-- The internal names of a type constructor declaration: its name and parameters. -/
def typeConstructor (acc : Acc) (tc : TypeConstructor) : Acc :=
  addAll (add acc tc.name) tc.params

mutual
/-- The internal names of a statement, including the labels of its blocks and exits. -/
def stmt (acc : Acc) : Statement → Acc
  | .cmd c => command acc c
  | .block l ss _ => block (add acc l) ss
  | .ite c ts es _ => block (block (exprOrNondet acc c) ts) es
  | .loop g m invs body _ =>
    let acc := exprOrNondet acc g
    let acc := match m with | some e => expr acc e | none => acc
    let acc := invs.foldl (fun acc (l, e) => expr (add acc l) e) acc
    block acc body
  | .exit l _ => add acc l
  | .typeDecl tc _ => typeConstructor acc tc
/-- `stmt` for each statement of a list. -/
def block (acc : Acc) : List Statement → Acc
  | [] => acc
  | s :: ss => block (stmt acc s) ss
end

/-- The internal names of a procedure body: its statements, or its block labels, commands and
    transfers; none for an abstract body. -/
def body (acc : Acc) : Procedure.Body → Acc
  | .structured ss _ => block acc ss
  | .cfg g _ =>
    g.blocks.foldl (init := add acc g.entry) fun acc (l, b) =>
      let acc := b.cmds.foldl command (add acc l)
      match b.transfer with
      | .condGoto p lt lf _ => add (add (expr acc p) lt) lf
      | .finish _ => acc
  | .abstract => acc

/-- The internal names of the labelled clauses of a contract. -/
def checks (acc : Acc) (cs : List (String × Procedure.Check)) : Acc :=
  cs.foldl (fun acc (l, c) => expr (add acc l) c.expr) acc

/-- The internal names of a procedure: its name, type parameters, parameters, lemma names,
    contract and body. -/
def procedure (acc : Acc) (p : Procedure) : Acc :=
  let acc := addAll (add acc p.header.name.name) p.header.typeArgs
  let acc := signature (signature acc p.header.inputs) p.header.outputs
  let acc := addAll acc p.header.lemmas
  body (checks (checks acc p.spec.preconditions) p.spec.postconditions) p.body

/-- The internal names of a function: its name, type parameters, parameters, output type, lemma
    names and expressions. -/
def function (acc : Acc) (f : Function) : Acc :=
  let acc := addAll (add acc f.name.name) f.typeArgs
  let acc := monoTy (signature acc f.inputs) f.output
  exprs (addAll acc f.lemmas) f.exprs

/-- The internal names of a datatype: its name, type parameters, constructors, their testers,
    fields and field types. -/
def datatype (acc : Acc) (d : LDatatype Unit) : Acc :=
  d.constrs.foldl (init := addAll (add acc d.name) d.typeArgs) fun acc c =>
    signature (add (add acc c.name.name) c.testerName) c.args

/-- The internal names of a type declaration. -/
def typeDecl (acc : Acc) : TypeDecl → Acc
  | .con tc => typeConstructor acc tc
  | .syn ts => monoTy (addAll (add acc ts.name) ts.typeArgs) ts.type
  | .data ds => ds.foldl datatype acc

/-- The internal names of a declaration, including the functions it introduces
    (`Decl.funcNames`), such as those a datatype declaration generates. -/
def decl (acc : Acc) (d : Decl) : Acc :=
  let acc := addAll acc (d.funcNames.map (·.name))
  match d with
  | .type t _ => typeDecl acc t
  | .ax a _ => expr (add acc a.name) a.e
  | .lemma l _ => expr (addAll (add acc l.name) l.typeArgs) l.e
  | .distinct n es _ => exprs (add acc n.name) es
  | .proc p _ => procedure acc p
  | .func f _ => function acc f
  | .recFuncBlock fs _ => fs.foldl function acc

end Program.InternalNames

/-- Every name of `p` in the namespace reserved for generated names (`Strata.Name.isInternal`): the
    names of declarations, of the functions they introduce, types, type parameters, constructors
    and testers, parameters, variables, operators, procedures called, labels of blocks, exits, CFG
    blocks, contract clauses and assertions, and the type names of every type and annotation. -/
@[expose] def Program.internalNames (p : Program) : List String :=
  -- The traversal adds internal names only; the filter states it where proofs can read it.
  (p.decls.foldl Program.InternalNames.decl #[]).toList.filter Strata.Name.isInternal

/-- The prefixes of the internal names of `p` (`Strata.Name.internalPrefixOf`), each once. -/
@[expose] def Program.collectIdentPrefixes (p : Program) : List String :=
  (p.internalNames.foldl (init := ({} : Std.HashSet String))
    fun s n => s.insert (Strata.Name.internalPrefixOf n)).toList

/-- The recorded prefixes of `p`, or, when none were recorded, the prefixes of its internal
    names, collected now. Either way they cover its internal names when every pass that added
    `$__` names to `p` recorded their prefixes. -/
@[expose] def Program.knownIdentPrefixes (p : Program) : List String :=
  p.usedIdentPrefixes.getD p.collectIdentPrefixes

/-- Does every internal name of `p` start with a prefix of `p.knownIdentPrefixes`? -/
@[expose] def Program.identPrefixesCovered (p : Program) : Bool :=
  let known := p.knownIdentPrefixes
  p.internalNames.all fun n => known.any fun q => n.startsWith q

/-- `p` recording the prefixes `pfxs` together with those it already records, each once. A
    program that records none records `pfxs` alone, so a caller passes every prefix the result
    has to cover. -/
@[expose] def Program.addIdentPrefixes (p : Program) (pfxs : List String) : Program :=
  { p with usedIdentPrefixes := some <|
      pfxs.foldl (fun l x => if l.contains x then l else l ++ [x]) (p.usedIdentPrefixes.getD []) }

/-- `p` with the prefixes of its internal names added to its recorded prefixes: they then cover
    its internal names. -/
def Program.withCollectedIdentPrefixes (p : Program) : Program :=
  p.addIdentPrefixes p.collectIdentPrefixes

/-- The known prefixes of `p` that are comparable with `pfx` (`Strata.Name.prefixesComparable`).
    When there are none and `p.identPrefixesCovered`, no internal name of `p` starts with `pfx`
    (`Program.not_startsWith_of_noConflict`). -/
@[expose] def Program.identPrefixConflicts (p : Program) (pfx : String) : List String :=
  p.knownIdentPrefixes.filter (Strata.Name.prefixesComparable pfx)

/-- Is no known prefix of `p` comparable with a prefix of `pfxs`? -/
@[expose] def Program.identPrefixesFree (p : Program) (pfxs : List String) : Bool :=
  let known := p.knownIdentPrefixes
  pfxs.all fun pfx => !known.any (Strata.Name.prefixesComparable pfx)

end Core

end -- public section
