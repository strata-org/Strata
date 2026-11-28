/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFG
public import Strata.Languages.Core.Function
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.TypeDecl
public import Strata.Languages.Core.Axiom
import Strata.Languages.Core.NameMangling
public import Strata.DL.Lambda.LExprTraversal
public import Strata.Languages.Core.DDMTransform.FormatCore

---------------------------------------------------------------------

public section

namespace Core

open Std (ToFormat Format format)
open Imperative

-- Type class instances needed for deriving and formatting
instance : Inhabited TypeDecl where
  default := .con { name := "DefaultType", params := [] }

-- ToFormat instance for Function (which is LFunc CoreLParams)
-- Note: ToFormat CoreLParams.Identifier is now defined in Identifiers.lean

inductive DeclKind : Type where
  | type | ax | lemma | distinct | proc | func | recFuncBlock
  deriving DecidableEq, Repr

instance : ToFormat DeclKind where
  format k := match k with
    | .type => "type"
    | .ax => "axiom"
    | .lemma => "lemma"
    | .distinct => "distinct"
    | .proc => "procedure"
    | .func => "function"
    | .recFuncBlock => "recursive functions"

/--
A Strata Core declaration.
Note: constants are 0-ary functions.
 -/
inductive Decl where
  /-- A type declaration (abstract type, type synonym, or algebraic datatype). -/
  | type (t : TypeDecl) (md : MetaData Core.Expression)
  /-- An axiom declaration. -/
  | ax   (a : Axiom) (md : MetaData Core.Expression)
  /-- A lemma declaration: a proposition that must be proved. -/
  | lemma (l : Lemma) (md : MetaData Core.Expression)
  /-- A `distinct` assertion: the given expressions are pairwise distinct. -/
  | distinct (name : Expression.Ident) (es : List Expression.Expr) (md : MetaData Core.Expression)
  /-- A procedure declaration. -/
  | proc (d : Procedure) (md : MetaData Core.Expression)
  /-- A function declaration. -/
  | func (f : Function) (md : MetaData Core.Expression)
  /-- A mutually recursive function block. -/
  | recFuncBlock (fs : List Function) (md : MetaData Core.Expression)
  deriving Inhabited, DecidableEq

def Decl.metadata (d : Decl) : MetaData Expression :=
  match d with
  | .type _ md       => md
  | .ax _ md         => md
  | .lemma _ md      => md
  | .distinct _ _ md => md
  | .proc _ md       => md
  | .func _ md       => md
  | .recFuncBlock _ md => md

@[expose] def Decl.kind (d : Decl) : DeclKind :=
  match d with
  | .type _ _   => .type
  | .ax _ _     => .ax
  | .lemma _ _  => .lemma
  | .distinct _ _ _ => .distinct
  | .proc _ _   => .proc
  | .func _ _   => .func
  | .recFuncBlock _ _ => .recFuncBlock

@[expose] def Decl.name (d : Decl) : Expression.Ident :=
  match d with
  | .type t _       => t.name
  | .ax a _         => a.name
  | .lemma l _      => l.name
  | .distinct n _ _ => n
  | .proc p _       => p.header.name
  | .func f _       => f.name
  | .recFuncBlock [] _ => ""
  | .recFuncBlock (f :: _) _ => f.name

/-- Get all names from a declaration. For mutual datatypes, returns all datatype names.
    For recFuncBlock, returns all function names. -/
@[expose] def Decl.names (d : Decl) : List Expression.Ident :=
  match d with
  | .type t _ => t.names
  | .recFuncBlock fs _ => fs.map (·.name)
  | _ => [d.name]

/-- The function names a declaration introduces: its functions (constants are 0-ary
    functions), and the eliminators, constructors, testers and destructors a datatype
    declaration generates, a nullary constructor being a constant too. -/
@[expose] def Decl.funcNames : Decl → List Expression.Ident
  | .func f _ => [f.name]
  | .recFuncBlock fs _ => fs.map (·.name)
  | .type (.data d) _ =>
    (Lambda.MutualDatatype.generatedFuncNames d).map fun n =>
      (⟨n, ()⟩ : Expression.Ident)
  | _ => []

/-- The names of the lemmas a declaration lists: a procedure's, and those of its functions. -/
@[expose] def Decl.lemmaNames : Decl → List String
  | .proc p _ => p.header.lemmas
  | .func f _ => f.lemmas
  | .recFuncBlock fs _ => fs.flatMap (·.lemmas)
  | _ => []

def Decl.getTypeDecl? (d : Decl) : Option TypeDecl :=
  match d with
  | .type t _ => some t
  | _ => none

def Decl.getAxiom? (d : Decl) : Option Axiom :=
  match d with
  | .ax a _ => some a
  | _ => none

def Decl.getTypeDecl (d : Decl) (H: d.kind = .type): TypeDecl :=
  match d with | .type t _ => t

@[expose] def Decl.getProc? (d : Decl) : Option Procedure :=
  match d with
  | .proc p _ => some p
  | _ => none

/-- Is `d` a procedure? -/
@[expose] def Decl.isProc (d : Decl) : Bool := d.kind == .proc

/-- The functions `d` declares: a function, or the members of a recursive block. -/
@[expose] def Decl.funcs : Decl → List Function
  | .func f _ => [f]
  | .recFuncBlock fs _ => fs
  | _ => []

def Decl.getProc (d : Decl) (H: d.kind = .proc): Procedure :=
  match d with | .proc p _ => p

def Decl.getFunc? (d : Decl) : Option Function :=
  match d with
  | .func f _ => some f
  | _ => none

def Decl.getFunc (d : Decl) (H: d.kind = .func): Function :=
  let .func f _ := d; f

def Decl.getRecFuncBlock? (d : Decl) : Option (List Function) :=
  match d with
  | .recFuncBlock fs _ => some fs
  | _ => none

/--
Build a constant declaration: `const name : ty;`, or `const name : ty := value;`
when `value` is given.

A constant is a nullary function, so this produces a `.func` declaration. See
`Core.Function.const` for the meaning of `value` and `attr`.
-/
def Decl.const (name : Expression.Ident) (ty : Lambda.LMonoTy)
    (value : Option Expression.Expr := none)
    (attr : Array Strata.DL.Util.FuncAttr := #[])
    (md : MetaData Expression := .empty) : Decl :=
  .func (Function.const name ty value attr) md

/-- The declaration of the opaque type `name`, which takes no type parameters. -/
def Decl.opaqueType (name : String) : Decl :=
  .type (.con { name := name, params := [] }) .empty

def Decl.eraseTypes (d : Decl) : Decl :=
  match d with
  | .ax a md     => .ax a.eraseTypes md
  | .lemma l md  => .lemma l.eraseTypes md
  | .proc p md   => .proc p.eraseTypes md
  | .func f md   => .func f.eraseTypes md
  | .recFuncBlock fs md => .recFuncBlock (fs.map (·.eraseTypes)) md
  | .type _ _ | .distinct _ _ _ => d

/-- Erase every annotation of a declaration: expression types, declared and signature types, and
    the type parameters of functions, procedures and lemmas, which the checker renames. Datatype
    and synonym type parameters are kept, since the checker never renames them. The expressions
    of a `distinct` declaration are erased, since the checker elaborates them. -/
def Decl.eraseAnnots (d : Decl) : Decl :=
  match d with
  | .type t md => .type t.eraseAnnots md
  | .ax a md => .ax a.eraseTypes md
  | .lemma l md => .lemma l.eraseAnnots md
  | .distinct n es md => .distinct n (es.map Lambda.LExpr.eraseTypes) md
  | .proc p md => .proc p.eraseAnnots md
  | .func f md => .func f.eraseAnnots md
  | .recFuncBlock fs md => .recFuncBlock (fs.map Function.eraseAnnots) md

/-- Remove all metadata from a declaration. -/
def Decl.stripMetaData (d : Decl) : Decl :=
  match d with
  | .type t _ => .type t .empty
  | .ax a _ => .ax a .empty
  | .lemma l _ => .lemma l .empty
  | .distinct n es _ => .distinct n es .empty
  | .proc p _ => .proc p.stripMetaData .empty
  | .func f _ => .func f .empty
  | .recFuncBlock fs _ => .recFuncBlock fs .empty

-- Metadata not included.
instance : ToFormat Decl where
  format d := match d with
    | .type t _md => f!"{t}"
    | .ax a _md  => f!"{a}"
    | .lemma l _md => f!"{l}"
    | .distinct l es _md  => f!"distinct [{l}] {es}"
    | .proc p _md => f!"{p}"
    | .func f _md => f!"{f}"
    | .recFuncBlock fs _md =>
      let fmts := fs.map (fun f => format f)
      f!"mutual{Format.line}{Format.joinSep fmts Format.line}{Format.line}end"

def Decl.formatWithMetaData (decl : Decl) : Format :=
  f!"{decl.metadata}{decl}"

abbrev Decls := List Decl

/-- A Core.Program is an ordered list of declarations. -/
structure Program where
  /-- The declarations that make up this program. -/
  decls : Decls
  /-- Prefixes of the names in the `$__` namespace, which is reserved for generated names, that
      the program may use, or `none` when they were not collected. The type-checking phase
      collects the prefixes of every such name of the program (`Program.internalNames`), so every
      such name starts with one of them (`Program.identPrefixesCovered`). A pass whose prefix no
      listed prefix is comparable with (`Program.identPrefixesFree`) can then name things with it
      without scanning the program. `none` makes a reader collect the prefixes first
      (`Program.knownIdentPrefixes`), so a program nobody scanned is never taken as free.

      No pass reads or extends the record yet: a pass that generates `$__` names does not add
      their prefixes, so after such a pass the record need not cover the program. -/
  usedIdentPrefixes : Option (List String) := none
  deriving DecidableEq

@[expose]
def Program.init : Program :=
  { decls := [] }

instance : Inhabited Program where
  default := .init

/-- The names of the types the program declares, at the top level or inside a structured
    procedure body. -/
def Program.typeNames (p : Program) : List String :=
  p.decls.flatMap fun
    | .type td _ => td.names.map (·.name)
    | .proc proc _ =>
      match proc.body with
      | .structured ss _ => (Imperative.Block.localTypeDecls ss).map (·.name)
      | .cfg _ _ | .abstract => []
    | _ => []

/-- The type names in the signatures of the procedures of `P`. -/
def Program.procSigTyNames (P : Program) : List String :=
  P.decls.flatMap fun
    | .proc q _ => (q.header.inputs.values ++ q.header.outputs.values).flatMap Lambda.getTypeRefs
    | _ => []

/-- The names in `names` that start with `pfx`. -/
def namesWithPrefix (names : List String) (pfx : String) : Std.HashSet String :=
  Std.HashSet.ofList (names.filter (·.startsWith pfx))

/-- The names of the types the program declares, at the top level or inside a procedure body,
    that start with `pfx`: the names a pass that names types with `pfx` must avoid. -/
def Program.typeNamesWithPrefix (p : Program) (pfx : String) : Std.HashSet String :=
  namesWithPrefix p.typeNames pfx

/-- Declarations that appear strictly before the first procedure named
    `procName`. If no such procedure exists, this is every declaration. -/
@[expose] def Program.declsBeforeProcedure (p : Program) (procName : String) : List Decl :=
  p.decls.takeWhile fun d =>
    match d with
    | .proc proc _ => proc.header.name.name != procName
    | _ => true

/-- Do the axioms and `distinct` declarations before the procedure named `procName` read
    no variable? Only `.fvar` nodes read the store. Constants and functions are `.op`
    nodes, which read the factory, so such declarations hold or fail in an environment by
    its factory alone (`Specification.AxiomsBeforeProcedureDecl.of_closed`). -/
@[expose] def Program.axiomsClosedBeforeProcedure (p : Program) (procName : String) : Bool :=
  (p.declsBeforeProcedure procName).all fun d =>
    match d with
    | .ax a _ => a.e.freeVars.isEmpty
    | .distinct _ es _ => es.all (·.freeVars.isEmpty)
    | _ => true

/-- Extend `factory` with the functions in `decl`: a function declaration
    adds itself, a recursive block adds all of its functions, and every other
    declaration leaves the factory unchanged. -/
@[expose] def Decl.addFunctionsToFactory
    (factory : Lambda.Factory CoreLParams) (decl : Decl) : Lambda.Factory CoreLParams :=
  match decl with
  | .func f _ => factory.pushIfNew f.toLFunc
  | .recFuncBlock fs _ =>
      fs.foldl (fun factory f => factory.pushIfNew f.toLFunc) factory
  | _ => factory

/-- Extend `factory` with the functions `decl` declares: a function or a recursive block
    adds its functions, as `Decl.addFunctionsToFactory` does, and a datatype block adds
    the functions `Lambda.genBlockFactory` generates for it. A block it rejects adds
    nothing; type checking rejects such a block. -/
@[expose] def Decl.addToRuntimeFactory
    (factory : Lambda.Factory CoreLParams) (decl : Decl) : Lambda.Factory CoreLParams :=
  match decl with
  | .type (.data block) _ =>
    match Lambda.genBlockFactory (T := CoreLParams) block with
    | .ok fs => factory.append fs.toArray
    | .error _ => factory
  | _ => decl.addFunctionsToFactory factory

/-- The initial expression factory visible at entry to the procedure named
    `procName`: Core's built-ins extended with the functions declared before that
    procedure, and with the constructors, testers, destructors and eliminators of the
    datatypes declared before it (`Decl.addToRuntimeFactory`). Later declarations are
    intentionally excluded. `pushIfNew` makes this total on malformed programs; program
    type checking rejects the name collisions that it would otherwise ignore. -/
@[expose] def Program.factoryBeforeProcedure
    (p : Program) (procName : String) : Lambda.Factory CoreLParams :=
  (p.declsBeforeProcedure procName).foldl Decl.addToRuntimeFactory Core.Factory

def Program.eraseTypes (p : Program) : Program :=
  { p with decls := p.decls.map Decl.eraseTypes }

/-- Erase every annotation of a program: expression types, declared types, the type
    parameters of functions, procedures and lemmas, and the recorded `$__` prefixes
    (`usedIdentPrefixes`), which the type-checking phase computes as it computes types. -/
def Program.eraseAnnots (p : Program) : Program :=
  { decls := p.decls.map Decl.eraseAnnots }

/-- Remove all metadata from a program. -/
def Program.stripMetaData (p : Program) : Program :=
  { p with decls := p.decls.map Decl.stripMetaData }

def Program.formatWithMetaData  (p : Program) : Format :=
  Std.Format.joinSep (List.map Decl.formatWithMetaData p.decls) Format.line

---------------------------------------------------------------------

@[expose]
def Program.find? (P : Program) (k : DeclKind) (x : Expression.Ident) : Option Decl :=
  go x P.decls
  where go x decls :=
  match decls with
  | [] => none
  | d :: drest =>
    if d.kind == k && d.name == x then d
    else go x drest

theorem Program.find?_kind : ∀ {p : Program}, (p.find? k x) = some d → d.kind = k := by
  intros p Hfind
  simp only [find?] at Hfind
  generalize Hdecls : p.decls = decls at Hfind
  induction decls generalizing p
  case nil =>
    unfold Program.find?.go at Hfind
    simp at Hfind
  case cons head tail ih =>
    unfold Program.find?.go at Hfind
    split at Hfind <;> simp_all
    next h =>
    exact ih (p := { decls := tail }) rfl

def Program.getAxiom? (P: Program) (n : Expression.Ident) : Option Axiom := do
  let decl ← P.find? .ax n
  let ax ← decl.getAxiom?
  return ax

/-- The function names the program's declarations introduce (`Decl.funcNames`). -/
def Program.funcNames (p : Program) : List String :=
  p.decls.flatMap fun d => d.funcNames.map (·.name)

@[expose]
def Program.getNames (P: Program) : List Expression.Ident :=
  go P.decls
  where go decls := decls.flatMap Decl.names

def Program.Type.find? (P : Program) (x : Expression.Ident) : Option TypeDecl :=
  match P.find? .type x with
  | none => none
  | some d => d.getTypeDecl?

def Program.Procedure.find? (P : Program) (x : Expression.Ident) : Option Procedure :=
  match H: (P.find? .proc x) with
  | none => none
  | some d => some $ d.getProc $ Program.find?_kind H

/-- A `String → Option Procedure` view of a `Program`, suitable for use as
    the `π` argument to the Core small-step semantics. -/
@[expose] def Program.findProcByString?
    (p : Program) (n : String) : Option Procedure :=
  (p.find? .proc ⟨n, ()⟩).bind Decl.getProc?

def Program.Function.find? (P : Program) (x : Expression.Ident)
  : Option Function :=
  go P.decls
where go
  | [] => none
  | .func f _ :: rest => if f.name == x then some f else go rest
  | .recFuncBlock fs _ :: rest =>
      match fs.find? (·.name == x) with
      | some f => some f
      | none => go rest
  | _ :: rest => go rest

-- accessor methods based on find?

theorem Program.findproc_some : (P.find? .proc x).isSome = (Procedure.find? P x).isSome := by
  simp [Procedure.find?, Option.isSome, Program.find?]
  split <;> simp
  . next x val heq =>
    split <;> simp
    next x' val' heq' =>
    split at heq' <;> simp_all
  . next od Heq =>
    split <;> simp
    next x' val' heq' =>
    split at heq' <;> simp_all

----------------------------------------------------------------

-- A deterministic version of find? that always returns the desired result.
def Program.find (P : Program) (k : DeclKind) (x : Expression.Ident) (H : (find? P k x).isSome = true)
  : Decl := (Program.find? P k x).get H

theorem Program.find_kind : ∀ (p : Program) {H: (p.find? k x).isSome = true}, (p.find k x H).kind = k := by
  intros p H
  simp [Program.find, Option.get]
  simp [Option.isSome] at H
  split
  next d' Hsome d Hsome' Heq Heq' =>
  split at H <;> try contradiction
  next x' val heq =>
  simp_all only [Option.some.injEq, heq_eq_eq]
  simp only [Option.isSome_some, Heq] at *
  expose_names
  apply find?_kind
  apply heq

theorem Program.find?find : ∀ P : Program,
    (P.find? k x) = some v ↔
    (exists H : (P.find? k x).isSome = true, (P.find k x H) = v) := by
  intros P
  exact Option.eq_some_iff_get_eq

def Program.Type.find (P: Program) (x : Expression.Ident) (H : (P.find? .type x).isSome = true)
  : TypeDecl
  := (P.find .type x H).getTypeDecl (find_kind P)

def Program.Procedure.find (P: Program) (x : Expression.Ident) (H : (P.find? .proc x).isSome = true)
  : Procedure
  := (P.find .proc x H).getProc (find_kind P)

def Program.Function.find (P: Program) (x : Expression.Ident) (H : (P.find? .func x).isSome = true)
  : Function :=
  (P.find .func x H).getFunc (find_kind P)

def Program.Procedure.findP? (P : Program) (x : Expression.Ident)
  : Option (Procedure ×' (find? P x).isSome = true) :=
  match Heq1 : (P.find? .proc x) with
  | some prog =>
    match Heq2 : prog.getProc? with
    | some proc =>
      let p : (find? P x).isSome = true := by
        simp [find?] at *
        split <;> simp_all
      some ⟨proc, p⟩
    | none => none
  | none => none

---------------------------------------------------------------------

/-! ## Statements and expressions of a whole program

A property of a program is stated as "every declaration's statements satisfy
`f`" or "every expression satisfies `P`". Only procedures carry statements, so
every other declaration satisfies a statement property vacuously; expressions,
on the other hand, are everywhere — in contracts, function bodies, axioms and
the guards of CFG transfers — and none of those are reachable from a
statement. -/

/-- The statements of `d`: a procedure's body, and nothing for any other
    declaration. -/
@[expose] def Decl.statements (d : Decl) : Statements :=
  match d with
  | Core.Decl.proc q _md => q.body.statements
  | _ => []

/-- Does `f` hold of every declaration's statements? -/
@[expose] def Decl.allStatements (f : Statements → Bool) (d : Decl) : Bool :=
  match d with
  | Core.Decl.proc q _md => q.body.allStatements f
  | _ => f []

/-- Does `f` hold of the statements of every procedure in `p`? -/
@[expose] def Program.allStatements (f : Statements → Bool) (p : Program) : Bool :=
  p.decls.all (Decl.allStatements f)

/-- The expressions `d` carries outside its statements: a procedure's contract
    and, in a CFG body, the guards of its transfers and the expressions in its
    blocks' metadata (`@[loopInvariant = (e)]`); a function's body, axioms,
    preconditions and measure; an axiom; a `distinct` fact. -/
@[expose] def Decl.ownExprs (d : Decl) : List Expression.Expr :=
  match d with
  | Core.Decl.proc q _md =>
    q.spec.preconditions.values.map (·.expr) ++
    q.spec.postconditions.values.map (·.expr) ++
    (match q.body with
     | .structured _ _ => []
     | .cfg g _ => g.blocks.flatMap fun (_, blk) =>
         blk.md.exprs ++
         match blk.transfer with
         | .condGoto p _ _ _ => [p]
         | .finish _ => []
     | .abstract => [])
  | Core.Decl.func f _md => f.exprs
  | Core.Decl.recFuncBlock fs _md => fs.flatMap (·.exprs)
  | Core.Decl.ax a _md => [a.e]
  | Core.Decl.lemma l _md => [l.e]
  | Core.Decl.distinct _ es _md => es
  | Core.Decl.type _ _md => []

/-- Does every expression in `p`, in a statement or not, satisfy `P`? -/
@[expose] def Program.allExprs (P : Expression.Expr → Bool) (p : Program) : Bool :=
  p.decls.all fun d =>
    (Statements.allExprs d.statements).all P && d.ownExprs.all P

/-- A set of names, joined by union: an accumulator for a fold over subterms. -/
structure NameUnion where
  names : Std.HashSet String := {}

instance : Append NameUnion :=
  ⟨fun a b => ⟨b.names.fold (init := a.names) fun s n => s.insert n⟩⟩

/-- A flag, joined by `||`: an accumulator for a fold over subterms. -/
structure AnyFlag where
  flag : Bool := false

instance : Append AnyFlag := ⟨fun a b => ⟨a.flag || b.flag⟩⟩

/-- The names of the operators `e` applies, visiting each physically distinct subterm once,
    so a term whose subterms are shared, as after symbolic evaluation, costs one walk of
    its graph rather than of its tree. -/
@[expose] def Expression.opNames (e : Expression.Expr) : Std.HashSet String :=
  (Lambda.LExpr.Traversal.visitDFSPtrCached .preorder
    (fun (e : Expression.Expr) => match e with
      | .op _ o _ => (⟨({} : Std.HashSet String).insert o.name⟩ : NameUnion)
      | _ => {})
    e).names

/-- Whether `e` contains an abstraction, visiting each physically distinct subterm once. -/
@[expose] def Expression.hasAbsShared (e : Expression.Expr) : Bool :=
  (Lambda.LExpr.Traversal.visitDFSPtrCached .preorder
    (fun (e : Expression.Expr) => match e with
      | .abs .. => (⟨true⟩ : AnyFlag)
      | _ => ⟨false⟩)
    e).flag

/-- The expressions of `p` the SMT back end can read: every expression of a procedure,
    an axiom, a lemma and a `distinct` declaration, which make the obligations and
    their path conditions, and the body and axioms of every function they reach, by
    name, through other reached functions' bodies and axioms. The back end emits a
    function's definition only when an emitted term applies it, so the bodies,
    axioms, preconditions and measures of the other functions never reach it. A
    function's preconditions and measure are not among the expressions read: the
    back end emits neither.

    The encoder chooses what to emit per query, by its own walk, so this whole-program
    set over-approximates each query's. A fact read over it, such as `noLambdas`, is
    accurate only while every function the encoder emits is one this set reaches. That
    is relied on but not proved; an encoder change that emits more must keep it. -/
@[expose] def Program.liveExprs (p : Program) : List Expression.Expr :=
  let funcs : List Function := p.decls.flatMap fun
    | .func f _ => [f]
    | .recFuncBlock fs _ => fs
    | _ => []
  let roots : List Expression.Expr := p.decls.flatMap fun d => match d with
    | .func .. | .recFuncBlock .. | .type .. => []
    | d => Statements.allExprs d.statements ++ d.ownExprs
  let read (f : Function) : List Expression.Expr := f.body.toList ++ f.axioms
  let union (es : List Expression.Expr) : Std.HashSet String :=
    es.foldl (fun acc e => (Expression.opNames e).fold (init := acc) fun s n => s.insert n) {}
  -- The operators each function's body and axioms apply, computed once per function.
  let funcOps : Std.HashMap String (Std.HashSet String) :=
    funcs.foldl (fun m f => m.insert f.name.name (union (read f))) {}
  let live : Std.HashSet String := Id.run do
    let mut found := union roots
    let mut frontier := found.toList
    -- Each round adds at least one function or stops, so `funcs.length + 1` rounds suffice.
    for _ in [0:funcs.length + 1] do
      let mut next : List String := []
      for n in frontier do
        for m in (funcOps.getD n {}).toList do
          if !found.contains m then
            found := found.insert m
            next := m :: next
      if next.isEmpty then break
      frontier := next
    return found
  roots ++ (funcs.filter (live.contains ·.name.name)).flatMap read

/-- The number of arguments each function `p` declares takes, by name: the
    declared inputs of a function, one per field for a datatype constructor, and
    one for a tester or a field selector. A monomorphized copy, whose name is
    mangled, is looked up under the name of the function it copies
    (`Program.arityIn`). -/
def Program.declArities (p : Program) : Std.HashMap String Nat :=
  p.decls.foldl (init := {}) fun m d =>
    match d with
    | .func f _ => m.insert f.name.name f.inputs.length
    | .recFuncBlock fs _ => fs.foldl (fun m f => m.insert f.name.name f.inputs.length) m
    | .type (.data block) _ => block.foldl (init := m) fun m dt =>
      let (cs, ts, ss, us) := dt.genFunctionMaps (T := CoreLParams)
      let m := cs.foldl (fun m (n, _, c) => m.insert n c.args.length) m
      [ts, ss, us].foldl (fun m fs => fs.foldl (fun m (n, _) => m.insert n 1) m) m
    | _ => m

/-- The number of arguments each function of `p` or `F` takes, by name, read from
    `arities`, the table `Program.declArities p` builds. Taking the table rather than
    the program lets a caller build it once for many lookups. -/
def Program.arityIn (arities : Std.HashMap String Nat) (F : @Lambda.Factory CoreLParams)
    (name : String) : Option Nat :=
  let lookup (n : String) := arities[n]? <|> (F[n]?).map (·.inputs.length)
  lookup name <|> lookup (Core.NameMangling.demangledBaseNameAnyPrefix name)

/-- Does no function `p` declares carry a precondition, whether declared at
    top level or inside a procedure body? -/
@[expose] def Program.noFuncPreconditions (p : Program) : Bool :=
  p.decls.all fun d =>
    (match d with
     | Core.Decl.func f _md => f.preconditions.isEmpty
     | Core.Decl.recFuncBlock fs _md => fs.all (·.preconditions.isEmpty)
     | _ => true)

/-- Does every function `p` declares, at the top level or in a recursive block, pass `c`? -/
@[expose] def Program.funcsAll (c : Function → Bool) (p : Program) : Bool :=
  p.decls.all fun d => d.funcs.all c

/-- The attributes of every function `p` declares, by name, including the functions of
    a recursive block. -/
def Program.funcAttrs (p : Program) : Std.HashMap String (Array Strata.DL.Util.FuncAttr) :=
  p.decls.foldl (init := {}) fun acc d =>
    match d with
    | .func fn _ => acc.insert fn.name.name fn.attr
    | .recFuncBlock fns _ => fns.foldl (fun a fn => a.insert fn.name.name fn.attr) acc
    | _ => acc

/-- Does no procedure in `p` carry a `requires` or `ensures` clause, free or
    checked? -/
@[expose] def Program.noProcedureContracts (p : Program) : Bool :=
  p.decls.all fun d =>
    match d with
    | Core.Decl.proc q _md =>
      q.spec.preconditions.isEmpty && q.spec.postconditions.isEmpty
    | _ => true

/-- Is every procedure in `p` monomorphic? Polymorphism is exactly a non-empty
    `header.typeArgs`, which is what `GenOpaqueTypeParams` clears; the opaque
    type declarations it adds in their place are ordinary declared sorts. -/
@[expose] def Program.noPolymorphicProcedures (p : Program) : Bool :=
  p.decls.all fun d =>
    match d with
    | Core.Decl.proc q _md => q.header.typeArgs.isEmpty
    | _ => true

/-- Is every function `p` declares monomorphic, wherever it is declared? Local
    declarations count as well as top-level ones, so lifting a function out of a
    procedure body does not change whether this holds. -/
@[expose] def Program.noPolymorphicFunctions (p : Program) : Bool :=
  p.decls.all fun d =>
    (match d with
     | Core.Decl.func f _md => f.typeArgs.isEmpty
     | Core.Decl.recFuncBlock fs _md => fs.all (·.typeArgs.isEmpty)
     | _ => true)

/-- Is `d` a procedure without a CFG body (its body is structured or abstract), or not a procedure
    at all? -/
@[expose] def Decl.isStructuredOrNonProc (d : Decl) : Bool :=
  match d with
  | Core.Decl.proc p _md => !p.body.isCfg
  | _ => true

/-- Does no procedure in `p` have a CFG body? Every body is structured or abstract. -/
@[expose] def Program.allStructured (p : Program) : Bool :=
  p.decls.all Decl.isStructuredOrNonProc

/-- Does no CFG body in `p` have a cycle reachable from its entry? A structured
    body has no CFG, so it passes whatever loops it holds. -/
@[expose] def Program.noCFGCycles (p : Program) : Bool :=
  p.decls.all fun d => match d with
    | Core.Decl.proc q _md => match q.body with
      | .cfg g _ => (Imperative.CFG.cycleLabelsWith g.succMap [g.entry]).isEmpty
      | .structured _ _ | .abstract => true
    | _ => true

/-- The calls in a declaration: a procedure's calls, and nothing for any other
    declaration. -/
def Decl.callSites : Decl → List CallSite
  | .proc q _ => Procedure.callSites q
  | _ => []

/-- Every call in `p`, in declaration order and then in order within each body. -/
def Program.callSites (p : Program) : List CallSite :=
  p.decls.flatMap Decl.callSites

/-! ## Axiom scopes -/

/-- The axioms declared before each procedure and each lemma of a program, by procedure or
    lemma name, in declaration order.  Symbolic evaluation and obligation extraction both
    scope axioms this way: the obligations of a procedure or a lemma assume exactly the axioms
    declared before it (`Program.eval`, and `ObligationExtraction.extractObligations` through
    `extractDecl`). -/
@[expose] def Program.axiomScopes (p : Program) : List (String × List Decl) :=
  (p.decls.foldl (init := (([] : List Decl), ([] : List (String × List Decl))))
    fun (axs, acc) d => match d with
      | .ax _ _ => (axs ++ [d], acc)
      | .proc q _ => (axs, acc ++ [(q.header.name.name, axs)])
      | .lemma l _ => (axs, acc ++ [(l.name, axs)])
      | _ => (axs, acc)).2

/-- The axioms and the procedure or lemma names of a program in declaration order, without the
    axioms after the last procedure or lemma: an axiom is `(some d, "")`, a procedure or lemma
    `(none, name)`. -/
@[expose] def Program.scopeEvents (p : Program) : List (Option Decl × String) :=
  let ev := p.decls.foldl (init := ([] : List (Option Decl × String))) fun acc d =>
    match d with
    | .ax _ _ => (some d, "") :: acc
    | .proc q _ => (none, q.header.name.name) :: acc
    | .lemma l _ => (none, l.name) :: acc
    | _ => acc
  (ev.dropWhile (·.1.isSome)).reverse

/-! ## Obligation procedures -/

/-- An obligation procedure: a procedure named `name` without type arguments, parameters or
    contract, with the structured body `body`. -/
@[expose] def Decl.obligationProc (name : CoreIdent) (body : Statements) : Decl :=
  Decl.proc {
      header := { name := name, typeArgs := [], inputs := [], outputs := [] },
      spec := { preconditions := [], postconditions := [] },
      body := .structured body false } .empty

end Core

---------------------------------------------------------------------

end -- public section
