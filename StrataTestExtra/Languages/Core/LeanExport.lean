/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.LeanExport

/-! # Lean export of validity queries

`ExportConfig.exportValidity` writes one Lean theorem file for a validity check in the
config's scope and changes nothing else. Core routing is exercised separately
in `LeanExportProgram`.

The export prints without a Lean environment. These tests have one, and use it
to check what the export cannot check itself: that the text of a file
elaborates to the expression it was printed from, up to the names of binders.
-/

open Lean Strata.SMT Strata.SMT.LeanExport Core.LeanExport Core.LeanExport.Tests

private def intVar (name : String) : UF := { id := name, args := [], out := .int }
private def call (uf : UF) : Strata.SMT.Term := .app (.uf uf) [] uf.out

private def x : UF := intVar "x"
private def xTerm : Strata.SMT.Term := call x
private def y : UF := intVar "y"
private def p : UF := { id := "p", args := [], out := .bool }

/-- `x * y / y = x`, given `0 ≤ x` and `0 < y`: a division. As context, assumptions and goal. -/
private def division : Core.SMT.Context × List Strata.SMT.Term × Strata.SMT.Term :=
  ({ ufs := .ofArray #[x, y] }, [.app .le [.int 0, xTerm] .bool, .app .lt [.int 0, call y] .bool],
    .app .eq [.app .div [.app .mul [xTerm, call y] .int, call y] .int, xTerm] .bool)

/-- `n` definitions, each using the one before: `cse_0 := 0`, `cse_i := cse_(i-1) + 1`. -/
private def cseChain (n : Nat) : List Core.VarDefinition :=
  (List.range n).map fun i =>
    { name := s!"cse_{i}", ty := .int,
      body := if i == 0 then .int 0 else .app .add [call (intVar s!"cse_{i - 1}"), .int 1] .int }

/-- `n` nested chained equalities `p = (…) = p`: the chain below is the middle operand. -/
private def chained (n : Nat) : Strata.SMT.Term :=
  (List.range n).foldl (fun (t : Strata.SMT.Term) _ => .app .eq [call p, t, call p] .bool) (call p)

/-- The label part of an exported file's name: the name without the hash of the proposition.
Compared with the labels exported, it tells that each check has one file and no other. -/
private def stem (file : System.FilePath) : String :=
  ((file.fileName.getD "").dropEnd "_0123456789abcdef.lean".length).toString

/-- The proposition text of an exported file: from the line after `def vcProp` to the first
blank line. -/
private def propositionOf (text : String) : Except String String :=
  match text.splitOn "def vcProp : Prop :=\n" with
  | [_, rest] => match rest.splitOn "\n\n" with
    | proposition :: _ :: _ => pure proposition
    | _ => throw "no blank line ends the proposition of the exported file"
  | _ => throw "the exported file does not define `vcProp` exactly once"

/-- Export one undecided check and return the text of the single file written. -/
private def exportOne (goal : Strata.SMT.Term) (definitions : List Core.VarDefinition := [])
    (ctx : Core.SMT.Context := {}) (assumptions : List Strata.SMT.Term := []) : IO String :=
  IO.FS.withTempDir fun dir => do
    let (config, events) ← recording dir
    config.exportValidity .unknown ctx assumptions goal definitions [] "one"
    let files ← leanFiles dir
    unless files.map stem == #["one"] do
      let diagnostics := (← events.get).map fun e => s!"{e.stage}: {e.diagnostic}"
      throw <| IO.userError s!"expected one exported file, got {files.size}; {diagnostics}"
    IO.FS.readFile files[0]!

/-- Export one undecided check that the export has to refuse for `reason`: it writes no file
and reports the refusal, once. -/
private def expectRefused (reason : String) (goal : Strata.SMT.Term)
    (ctx : Core.SMT.Context := {}) (assumptions : List Strata.SMT.Term := [])
    (configure : ExportConfig → ExportConfig := id) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let (config, events) ← recording dir
    (configure config).exportValidity .unknown ctx assumptions goal [] [] "refused"
    let seen ← events.get
    unless (← leanFiles dir).isEmpty && seen.size == 1 && seen.all (fun e =>
        e.stage == .preparationFailure && e.file.isNone && has e.diagnostic reason) do
      throw <| IO.userError s!"expected one refusal saying `{reason}`, got \
        {seen.map fun e => (e.stage, e.diagnostic)}"

/-- Unfold the `let` bindings in an expression. The printer binds a subterm that occurs
several times by a `let`; the translator's own definitions are `have` bindings and stay. -/
private partial def unshare (e : Expr) : Expr :=
  e.replace fun
    | .letE _ _ value body false => some (unshare (body.instantiate1 (unshare value)))
    | _ => none

/-- The exported text of a query elaborates to the expression it was printed from, identical
up to binder names once the `let` bindings of shared subterms are unfolded: not merely an
equivalent or definitionally equal one. Binder names are no part of the comparison, because
the file does not keep them all: the printer renames a binder apart from an enclosing binder
and from a constant, and Lean names the hypothesis of an arrow itself. A case that depends on
a name asserts it on the text. The text is elaborated here, in this file's environment and
with the namespaces it opens; that a file needs neither is what `compilesAlone` checks.
Returns the proposition text and the text of the whole file. -/
private def readsBackIdentical (name : String) (goal : Strata.SMT.Term)
    (definitions : List Core.VarDefinition := []) (ctx : Core.SMT.Context := {})
    (assumptions : List Strata.SMT.Term := []) : Elab.TermElabM (String × String) := do
  let query ← prepare ctx assumptions goal definitions []
  let text ← liftM (m := IO) <| exportOne goal definitions ctx assumptions
  let proposition ← ofExcept (propositionOf text)
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term proposition)
  let elaborated ← withOptions (·.set `maxRecDepth (100000 : Nat)) do
    let e ← Elab.Term.withoutErrToSorry <| Elab.Term.elabTerm stx (some (mkSort Level.zero))
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  unless unshare elaborated == unshare query.validity do
    throwError "{name}: the exported text elaborates to a different expression"
  return (proposition, text)

-- Integer arithmetic with division, a comparison that decides an `if`, bit-vectors and a
-- long chain of definitions.
#guard_msgs in
run_elab do
  let (ctx, assumptions, goal) := division
  let _ ← readsBackIdentical "division" goal (ctx := ctx) (assumptions := assumptions)
  let smaller : Strata.SMT.Term := .app .ite [.app .lt [xTerm, call y] .bool, xTerm, call y] .int
  let _ ← readsBackIdentical "if on a comparison" (ctx := { ufs := .ofArray #[x, y] })
    (.app .le [smaller, xTerm] .bool)
  let a : UF := { id := "a", args := [], out := .bitvec 64 }
  let b : UF := { id := "b", args := [], out := .bitvec 64 }
  let mixed := (List.range 10).foldl (fun t i =>
    .app (.bv .bvxor) [.app (.bv .bvadd) [t, call b] (.bitvec 64),
      .app (.bv .bvmul) [call a, .prim (.bitvec (BitVec.ofNat 64 (i + 3)))] (.bitvec 64)]
      (.bitvec 64)) (call a)
  let _ ← readsBackIdentical "bit-vectors" (ctx := { ufs := .ofArray #[a, b] })
    (.app .eq [mixed, mixed] .bool)
  let _ ← readsBackIdentical "ninety definitions"
    (.app .eq [call (intVar "cse_89"), .int 89] .bool) (cseChain 90)

-- An `if` whose condition is itself an `if`, fifteen levels deep. The condition stands in the
-- instance of each `if` as well; were it written out in both places, the text would double
-- per level. It is written once and bound by a `let`.
#guard_msgs in
run_elab do
  let nested := (List.range 15).foldl (fun (t : Strata.SMT.Term) (i : Nat) =>
    .app .ite [t, .app .lt [xTerm, .int i] .bool, .app .lt [call y, .int i] .bool] .bool)
    (.app .lt [xTerm, call y] .bool)
  let (text, _) ← readsBackIdentical "nested conditions" (ctx := { ufs := .ofArray #[x, y] })
    (.app .or [nested, .app .not [nested] .bool] .bool)
  unless text.length < 40000 do
    throwError "nested conditions are written out more than once: {text.length} characters"

-- A shallow but wide goal.
#guard_msgs in
run_elab do
  let leaf : Strata.SMT.Term := .app .eq [xTerm, xTerm] .bool
  let goal := (List.range 11).foldl (fun term _ => .app .and [term, term] .bool) leaf
  let _ ← readsBackIdentical "wide" goal (ctx := { ufs := .ofArray #[x] })

-- Names that are Lean keywords, names of the constants the proposition uses, and names with
-- unusual characters are still identifiers in the file, and none captures another.
#guard_msgs in
run_elab do
  let names := ["end", "fun", "if", "then", "at", "Int", "HAdd", "Eq", "ite", "a b", "x@1",
    "$__cse.6", "x.y", "«", "+"]
  let vars := names.map intVar
  let sum := vars.foldl (fun t v => .app .add [t, call v] .int) (.int 0)
  let (text, _) ← readsBackIdentical "names" (ctx := { ufs := .ofArray vars.toArray })
    (.app .eq [sum, sum] .bool)
  -- A variable named like a constant in use is renamed, so the constant is still meant.
  unless has text "«Int_1»" && has text "@Int" do
    throwError "a variable named `Int` was not kept apart from the type"
  -- A quantified variable of the same name as a declared one is renamed apart from it.
  let goal : Strata.SMT.Term := .app .eq [xTerm, xTerm] .bool
  let bound : TermVar := ⟨"x", .int⟩
  let (text, _) ← readsBackIdentical "shadowing" (ctx := { ufs := .ofArray #[x] }) goal
    (assumptions := [.quant .all [bound] [] (.app .le [.var bound, .var bound] .bool)])
  unless has text "(∀ («x_1» : @Int),\n" && has text " «x_1» «x_1»))" && has text " «x» «x»)" do
    throwError "a quantified `x` was not kept apart from the declared `x`: {text}"
  -- A body that also uses the declared `x` has no such form: in the solver's format the name
  -- means the quantified variable there. The query is refused.
  expectRefused "Symbol 'x' is shadowed by an SMT binder" goal (ctx := { ufs := .ofArray #[x] })
    (assumptions := [.quant .all [bound] [] (.app .le [.var bound, xTerm] .bool)])
  -- Two quantifications that differ in the name of the variable only are equal expressions
  -- to Lean. Each is written with its own name.
  let below (name : String) : Strata.SMT.Term :=
    .quant .exist [⟨name, .int⟩] [] (.app .le [.var ⟨name, .int⟩, xTerm] .bool)
  let (text, _) ← readsBackIdentical "equal up to names" (ctx := { ufs := .ofArray #[x] })
    (.app .and [below "a", below "b"] .bool)
  unless has text "(fun («a» : @Int) =>" && has text "(fun («b» : @Int) =>" do
    throwError "a quantification was written with the variable name of another: {text}"

-- A function that a term applies and the context does not declare is declared in the file,
-- as the solver's encoder declares it on first use.
#guard_msgs in
run_elab do
  let g : UF := { id := "g", args := [.int], out := .int }
  let applied : Strata.SMT.Term := .app (.uf g) [xTerm] .int
  let (text, _) ← readsBackIdentical "declared on first use" (ctx := { ufs := .ofArray #[x] })
    (.app .eq [applied, applied] .bool)
  unless has text "∀ («g» : (@Int →\n@Int))," do
    throwError "a function declared on first use is not bound in the exported proposition"

-- A binder is renamed when an enclosing binder already uses its name, so that no reference
-- is captured. Names with no identifier form are all written `x`; here they stand beside
-- variables really named `x` and `x_1`, and under a quantifier whose body refers to the
-- declared `x`.
#guard_msgs in
run_elab do
  let vars := ["»", "a»b", "x", "x_1", "line\nbreak"].map intVar
  let sum := vars.foldl (fun t v => .app .add [t, call v] .int) (.int 0)
  let inner : TermVar := ⟨"b»", .int⟩
  let (text, _) ← readsBackIdentical "renamed binders" (ctx := { ufs := .ofArray vars.toArray })
    (.app .eq [sum, sum] .bool)
    (assumptions := [.quant .all [inner] [] (.app .le [.var inner, xTerm] .bool)])
  let binders := ((text.splitOn "∀ («").drop 1).map fun rest => (rest.splitOn "»").headD ""
  unless binders.length == 6 && binders.eraseDups.length == 6 do
    throwError "binders that share a name were not renamed apart: {binders}"

-- The other binding forms: an existential (a `fun`), a definition with parameters (a `have`
-- of a function), and a sort alias.
#guard_msgs in
run_elab do
  let y : TermVar := ⟨"y", .int⟩
  let (text, _) ← readsBackIdentical "existential" (ctx := { ufs := .ofArray #[x] })
    (.quant .exist [y] [] (.app .lt [xTerm, .var y] .bool))
  unless has text "(fun («y» : @Int) =>" do
    throwError "an existential is not written as a function: {text}"
  let a : TermVar := ⟨"a", .int⟩
  let b : TermVar := ⟨"b", .int⟩
  let larger : Strata.SMT.IF := {
    id := "larger", args := [a, b], out := .int
    body := .app .ite [.app .lt [.var a, .var b] .bool, .var b, .var a] .int }
  let (text, _) ← readsBackIdentical "definition with parameters"
    (ctx := { ufs := .ofArray #[x], ifs := .ofArray #[larger] })
    (.app .le [xTerm, .app (.uf larger.toUF) [xTerm, .int 0] .int] .bool)
  unless has text "have «larger» : " && has text "(fun («a» : @Int) =>" do
    throwError "a definition with parameters is not a `have` of a function: {text}"
  let alias : TermType := .constr "Alias" []
  let c : UF := { id := "c", args := [], out := alias }
  let _ ← readsBackIdentical "sort alias"
    (ctx := { tySubst := [("Alias", .int)], ufs := .ofArray #[c] })
    (.app .eq [call c, call c] .bool)

-- A sort alias the query does not use is no part of it, whatever it stands for: the file is
-- the one written without the alias. An alias in use, also through another alias, is kept.
#guard_msgs in
run_elab do
  let goal : Strata.SMT.Term := .app .eq [xTerm, xTerm] .bool
  let (plain, _) ← readsBackIdentical "no alias" (ctx := { ufs := .ofArray #[x] }) goal
  for (name, target) in [("M", TermType.constr "Array" [.int, .int]), ("R", .real)] do
    let (text, _) ← readsBackIdentical s!"unused alias {name}"
      (ctx := { ufs := .ofArray #[x], tySubst := [(name, target)] }) goal
    unless text == plain do
      throwError "an unused sort alias changed the exported proposition: {text}"
  let outer : TermType := .constr "Outer" []
  let c : UF := { id := "c", args := [], out := outer }
  let _ ← readsBackIdentical "alias of an alias"
    (ctx := { tySubst := [("Inner", .int), ("Outer", .constr "Inner" []), ("R", .real)],
              ufs := .ofArray #[c] })
    (.app .eq [call c, call c] .bool)

/-- Export `goal`, without context, as the check `same-label` answered with `answer`. -/
private def exportSameLabel (config : ExportConfig) (answer : Answer)
    (goal : Strata.SMT.Term := .bool true) : IO Unit :=
  config.exportValidity answer {} [] goal [] [] "same-label"

-- A validity result of the per-obligation path as an answer. Core reports an error result
-- whose message names a timeout as a solver error. The export reads it as a timeout: a check
-- the solver gave up on for time is undecided, and belongs to the default scope.
#guard Answer.ofResult .unsat == .proved
#guard Answer.ofResult (.sat []) == .refuted
#guard Answer.ofResult (.unknown none) == .unknown
#guard Answer.ofResult (.err "interrupted by timeout.") == .timeout
#guard Answer.ofResult (.err "native error") == .error
-- A session that walks several checks may hold more than the query of one: its `unsat` is
-- an answer of its own.
#guard Answer.ofSessionDecision .unsat == .provedInSession
#guard Answer.ofSessionDecision .sat == .refuted
#guard Answer.ofSessionDecision .timeout == .timeout
#guard Answer.ofSessionDecision .unknown == .unknown
#guard [Answer.proved, .provedInSession, .refuted, .error, .notAsked].all
  (!Scope.undecided.covers ·)
#guard [Answer.unknown, .timeout].all (Scope.undecided.covers ·)
#guard [Answer.proved, .provedInSession, .refuted, .error, .notAsked, .unknown, .timeout].all
  (Scope.all.covers ·)

-- The default scope covers the checks the solver left undecided, and only those. The scope
-- `all` covers every validity check, whatever the solver answered, asked or not. Each check
-- is exported into a directory of its own: its file reports the answer to that check, and
-- leaves the theorem open.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    let answers : List (Answer × String × Bool) := [
      (.proved, "unsat (the solver found the query valid)", false),
      (.provedInSession,
        "unsat (in a solver session that may hold more than this query states)", false),
      (.refuted, "sat (the solver found a counterexample)", false),
      (.error, "error", false), (.notAsked, "not asked", false),
      (.unknown, "unknown", true), (.timeout, "timeout", true)]
    for (scopeName, scope) in [("undecided", Scope.undecided), ("all", Scope.all)] do
      for (answer, verdict, undecided) in answers do
        let dir := root / scopeName / verdict
        let (config, events) ← recording dir scope
        exportSameLabel config answer
        let stages := (← events.get).map (·.stage)
        let files ← leanFiles dir
        let texts ← files.mapM IO.FS.readFile
        if scope == .all || undecided then
          unless stages == #[.exported] && files.map stem == #["same-label"] &&
              texts.all (has · s!"-- Solver's answer: {verdict}\n") do
            throw <| IO.userError s!"Scope `{scopeName}`: the check answered `{verdict}` has \
              no file of its own that reports this answer: {stages}, {texts}"
          unless texts.all (has · "theorem vc : vcProp := by\n  unfold vcProp\n  sorry\n") do
            throw <| IO.userError "An exported file does not leave its theorem open"
        else unless stages.isEmpty && !(← dir.pathExists) do
          throw <| IO.userError s!"Scope `{scopeName}`: the check answered `{verdict}` was \
            exported or reported: {stages}"

-- A query with no Lean form writes no file and says why.
#guard_msgs in
run_elab do
  let realVar : UF := { id := "r", args := [], out := .real }
  let real : Strata.SMT.Term := .app (.uf realVar) [] .real
  expectRefused "unsupported sort 'Real'" (.app .eq [real, real] .bool)
    (ctx := ({} : Core.SMT.Context).addUF realVar)
  -- A string, also as a literal: the solver's strings are not Lean's.
  expectRefused "unsupported sort 'String'"
    (.app .eq [.prim (.string "a"), .prim (.string "a")] .bool)

-- A file that exists is not overwritten: it states the same theorem, and its proof may have
-- been filled in. Here the proof is, and the file stays as the user left it.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let (config, events) ← recording dir
    exportSameLabel config .unknown
    let files ← leanFiles dir
    unless files.map stem == #["same-label"] do throw <| IO.userError "The check was not exported"
    let exported ← IO.FS.readFile files[0]!
    let filled := exported.replace "\n  sorry\n" "\n  exact True.intro\n"
    unless filled != exported do throw <| IO.userError "The open proof is not the line `sorry`"
    IO.FS.writeFile files[0]! filled
    exportSameLabel config .unknown
    unless (← leanFiles dir) == files && (← IO.FS.readFile files[0]!) == filled do
      throw <| IO.userError "A file with its proof filled in was overwritten"
    let seen ← events.get
    unless seen.map (·.stage) == #[.exported, .kept] && seen.all (·.file == some files[0]!) do
      throw <| IO.userError s!"A kept file was not reported as kept: {seen.map (·.stage)}"

-- A later run that gets another answer to the same check keeps the file as well, header
-- included: the header reports the answer of the run that wrote the file.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    exportSameLabel { directory := dir } .unknown
    let files ← leanFiles dir
    let exported ← files.mapM IO.FS.readFile
    unless files.map stem == #["same-label"] &&
        exported.all (has · "-- Solver's answer: unknown\n") do
      throw <| IO.userError "The check was not exported with its answer"
    let (later, events) ← recording dir (scope := .all)
    exportSameLabel later .timeout
    exportSameLabel later .proved
    unless (← leanFiles dir) == files && (← files.mapM IO.FS.readFile) == exported do
      throw <| IO.userError "A later answer changed the file of an earlier run"
    unless (← events.get).map (·.stage) == #[.kept, .kept] do
      throw <| IO.userError "A later run did not report the file of an earlier run as kept"

-- A file that cannot be written is reported and nothing is thrown; an observer that fails
-- does not stop the export either.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    let blocked := root / "not-a-directory"
    IO.FS.writeFile blocked ""
    let (config, events) ← recording (blocked / "out")
    exportSameLabel config .unknown
    let seen ← events.get
    unless seen.size == 1 && seen.all (fun e =>
        e.stage == .writeFailure && e.file.isNone && !e.diagnostic.isEmpty) do
      throw <| IO.userError s!"A failed write was not reported as one: {seen.map (·.stage)}"
    let failing : ExportConfig := {
      directory := root / "out", observe := fun _ => throw <| IO.userError "observer failed" }
    exportSameLabel failing .unknown
    unless (← leanFiles (root / "out")).map stem == #["same-label"] do
      throw <| IO.userError "A failing observer kept the file from being written"

-- File names and contents depend on the label and the proposition only: checks exported
-- concurrently, in any order and in different runs, give the same files, one per distinct
-- proposition. Of the concurrent checks of one proposition, one writes the file and the
-- others keep it.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    let (first, events) ← recording (root / "first")
    let tasks ← (List.range 8).mapM fun i => IO.asTask do
      exportSameLabel first .unknown (.bool (i % 2 == 0))
    for task in tasks do IO.ofExcept task.get
    let second : ExportConfig := { directory := root / "second" }
    exportSameLabel second .unknown (.bool false)
    exportSameLabel second .unknown (.bool true)
    let stages := (← events.get).map (·.stage)
    unless stages.size == 8 && stages.count .exported == 2 && stages.count .kept == 6 do
      throw <| IO.userError s!"Eight concurrent checks of two propositions were not exported \
        twice and kept six times: {stages}"
    let files ← leanFiles (root / "first")
    let again ← leanFiles (root / "second")
    unless files.map stem == #["same-label", "same-label"] &&
        files.map (·.fileName) == again.map (·.fileName) &&
        (← files.mapM IO.FS.readFile) == (← again.mapM IO.FS.readFile) do
      throw <| IO.userError "The files depend on more than the label and the proposition"

-- An exported file compiles on its own: no import, and only the open proof is reported. That
-- holds for a proposition far deeper than Lean's default recursion limit allows and longer
-- than the size from which a file lifts Lean's time limit, so that the file lifts both: a
-- thousand definitions that each use the one before, and a thousand premises.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let config : ExportConfig := { directory := dir }
    let (ctx, assumptions, goal) := division
    config.exportValidity .unknown ctx assumptions goal [] [] "division"
    config.exportValidity .unknown { ufs := .ofArray #[x] }
      ((List.range 1000).map fun (i : Nat) => .app .le [.int i, xTerm] .bool)
      (.app .eq [call (intVar "cse_999"), .int 999] .bool) (cseChain 1000) [] "deep"
    let files ← leanFiles dir
    unless files.map stem == #["deep", "division"] do
      throw <| IO.userError "The queries were not both exported"
    let deep ← IO.FS.readFile files[0]!
    -- The time limit is lifted for the definition and for the theorem, which states it again.
    unless has deep "\nset_option maxRecDepth " &&
        has deep "\nset_option maxHeartbeats 0 in\nset_option linter.unusedVariables false in\n\
          def vcProp" &&
        has deep "\nset_option maxHeartbeats 0 in\ntheorem vc : vcProp" do
      throw <| IO.userError "The deep proposition does not lift the recursion and time limits"
    for file in files do compilesAlone file

-- A label is one comment line of the file, whatever it contains: a line break in it starts
-- no line of Lean.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let config : ExportConfig := { directory := dir }
    config.exportValidity .unknown {} [] (.bool true) [] []
      "first\ntheorem injected : False := sorry\rend"
    let files ← leanFiles dir
    unless files.map stem == #["first_theorem_injected___False____sorry_end"] do
      throw <| IO.userError "The check was not exported under the name of its label"
    unless (← IO.FS.readFile files[0]!).startsWith "-- Strata verification condition: \
        first theorem injected : False := sorry end\n-- Solver's answer: unknown\n" do
      throw <| IO.userError "A label with line breaks is not one comment line"
    -- The header says what a proof of the file rests on.
    unless has (← IO.FS.readFile files[0]!) "as far as that\n\
        -- translation is faithful, which is tested and reviewed, not proved" do
      throw <| IO.userError "The header does not say that the translation is not proved"
    compilesAlone files[0]!

-- A check of a program is not exported when one of its variables, declared or defined, has
-- the name of a function of the program; it is reported once, when the scope covers it.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    let c := call (intVar "c")
    let goal : Strata.SMT.Term := .app .eq [c, c] .bool
    -- The clashing variable is the first, the middle and the last of a list of three.
    let declare (name : String) : Core.VarDeclaration := { name, ty := .int }
    let define (name : String) : Core.VarDefinition := { name, ty := .int, body := .int 0 }
    let orders := [["c", "z", "w"], ["z", "c", "w"], ["z", "w", "c"]]
    let cases : List (String × List Core.VarDefinition × List Core.VarDeclaration ×
        Bool × Answer × Array Stage) :=
      orders.flatMap (fun names => [
        (s!"declared {names}", [], names.map declare, true, .unknown, #[.preparationFailure]),
        (s!"defined {names}", names.map define, [], true, .unknown, #[.preparationFailure])]) ++
      [("out of scope", ["z", "c", "w"].map define, [], true, .proved, #[]),
       ("no function", ["z", "c", "w"].map define, [], false, .unknown, #[.exported])]
    for (name, definitions, declarations, isFunction, answer, stages) in cases do
      let (config, events) ← recording (root / name)
      config.exportCheck (·.find? fun name => isFunction && name == "c") answer {} [] goal
        definitions declarations "d"
      unless (← events.get).map (·.stage) == stages &&
          ((← leanFiles (root / name)).size == 1) == (stages == #[.exported]) do
        throw <| IO.userError s!"{name}: unexpected events {(← events.get).map (·.stage)}"

-- A label that would give a hidden file, a name read as an option, or no name gets the
-- prefix `vc`. A label longer than 96 characters is cut to its first 96.
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let config : ExportConfig := { directory := dir }
    let long := String.ofList (List.replicate 120 'a')
    for label in [".hidden", "-o", "", "café_α", long] do
      config.exportValidity .unknown {} [] (.bool true) [] [] label
    -- Of the letters and digits, only the ASCII ones are kept: `é` and `α` become `_`.
    unless (← leanFiles dir).map stem ==
        #[(long.take 96).toString, "caf___", "vc-o", "vc.hidden", "vc"] do
      throw <| IO.userError s!"Unexpected file names: {← leanFiles dir}"

/-! ## Division and modulo

SMT-LIB leaves an integer division or modulo by zero open, and the translator keeps it open
in the file: it binds `divByZero modByZero : Int → Int` in front of a query that divides and
writes `div x y` as `if y = 0 then divByZero x else x / y`, `mod` alike with `modByZero`.
The export has no check of its own behind the translator, so these tests look at the
expression each file is printed from, wherever a division can stand. -/

/-- The numbers of integer divisions and modulos in `e`, an expression under `depth` binders
of which the two outermost are the translator's `divByZero` and `modByZero`. `none` unless
each division is the last operand of the zero test on its own operands,
`@ite Int (y = 0) (Int.decEq y 0) (divByZero x) (x / y)`, and each modulo alike with
`modByZero`: Lean's value at a zero divisor (`x / 0 = 0`, `x % 0 = x`) is then read nowhere.
The translator writes an integer division and modulo as `HDiv.hDiv` and `HMod.hMod`. -/
private partial def zeroTested (depth : Nat) (e : Expr) : Option (Nat × Nat) :=
  let sum (parts : List (Nat × Expr)) : Option (Nat × Nat) :=
    parts.foldlM (init := (0, 0)) fun (divisions, modulos) (depth, e) => do
      let (d, m) ← zeroTested depth e
      pure (divisions + d, modulos + m)
  -- How far out the binder of the value at zero is: 1 for a division, 2 for a modulo.
  let byZero? (e : Expr) : Option Nat :=
    if e.isAppOfArity ``HDiv.hDiv 6 then some 1
    else if e.isAppOfArity ``HMod.hMod 6 then some 2 else none
  match e with
  | .app .. =>
    let args := e.getAppArgs
    match if e.isAppOfArity ``ite 5 then byZero? args[4]! else none with
    | some binder => do
      let x := args[4]!.getArg! 4
      let y := args[4]!.getArg! 5
      let zero := toExpr (0 : Int)
      guard <| binder ≤ depth && args[0]! == mkConst ``Int &&
        args[1]! == mkApp3 (.const ``Eq [1]) (mkConst ``Int) y zero &&
        args[2]! == mkApp2 (mkConst ``Int.decEq) y zero &&
        args[3]! == .app (.bvar (depth - binder)) x
      let (divisions, modulos) ← sum [(depth, x), (depth, y)]
      pure (if binder == 1 then (divisions + 1, modulos) else (divisions, modulos + 1))
    | none => do
      guard (byZero? e).isNone
      sum ((e.getAppFn :: args.toList).map (depth, ·))
  | .lam _ t b _ | .forallE _ t b _ => sum [(depth, t), (depth + 1, b)]
  | .letE _ t v b _ => sum [(depth, t), (depth, v), (depth + 1, b)]
  | .mdata _ e => zeroTested depth e
  | _ => pure (0, 0)

-- `zeroTested` on expressions written by hand, with `d` and `m` for the two binders: it
-- counts a tested division and a tested modulo, and refuses a division that is not tested,
-- one tested on another divisor, one whose value at zero is the other binder's or is taken
-- at another dividend, and one in the branch of the zero divisor.
#guard_msgs in
run_elab do
  let cases : List (String × Option (Nat × Nat)) := [
    ("@ite Int (@Eq Int y 0) (Int.decEq y 0) (d x) (x / y)", some (1, 0)),
    ("@ite Int (@Eq Int y 0) (Int.decEq y 0) (m x) (x % y)", some (0, 1)),
    ("x / y", none),
    ("@ite Int (@Eq Int x 0) (Int.decEq x 0) (d x) (x / y)", none),
    ("@ite Int (@Eq Int y 0) (Int.decEq y 0) (m x) (x / y)", none),
    ("@ite Int (@Eq Int y 0) (Int.decEq y 0) (d y) (x / y)", none),
    ("@ite Int (@Eq Int y 0) (Int.decEq y 0) (x / y) (d x)", none)]
  for (body, expected) in cases do
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term
      s!"fun (d m : Int → Int) (x y : Int) => {body}"
    let e ← Elab.Term.elabTerm stx none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    -- The elaborator annotates an argument of `Int.decEq`; the translator's expression has no
    -- annotations.
    let e := (← instantiateMVars e).replace fun | .mdata _ e => some e | _ => none
    unless zeroTested 0 e == expected do
      throwError "zeroTested does not give {expected} on `{body}`"

/-- Export `goal` and check the file: its text has fewer than `limit` bytes, reads back
identical and compiles on its own, and the expression it is printed from has `divisions`
divisions and `modulos` modulos, each of them zero-tested (`zeroTested`), under the binders
`divByZero modByZero : Int → Int`, which stand in front exactly when the query divides (a
sort alias would stand before them; no query here has one). Returns the exported text. -/
private def dividedExport (name : String) (divisions modulos : Nat) (goal : Strata.SMT.Term)
    (limit : Nat := 20000) (definitions : List Core.VarDefinition := [])
    (ctx : Core.SMT.Context := {}) (assumptions : List Strata.SMT.Term := []) :
    Elab.TermElabM String := do
  let (_, text) ← readsBackIdentical name goal definitions ctx assumptions
  unless text.utf8ByteSize < limit do
    throwError "{name}: the exported text has {text.utf8ByteSize} bytes, not fewer than {limit}"
  let intToInt := Lean.mkForall .anonymous .default (mkConst ``Int) (mkConst ``Int)
  let counted := match (← prepare ctx assumptions goal definitions []).validity with
    | .forallE `divByZero s (.forallE `modByZero t body _) _ =>
      if s == intToInt && t == intToInt && divisions + modulos > 0 then zeroTested 2 body
      else none
    | validity => if divisions + modulos == 0 then zeroTested 0 validity else none
  unless counted == some (divisions, modulos) do
    throwError "{name}: the divisions and modulos of the exported proposition are {counted}, \
      not {divisions} and {modulos} that are each tested for a zero divisor under the binders \
      `divByZero` and `modByZero`: {text}"
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let file := dir / "Export.lean"
    IO.FS.writeFile file text
    compilesAlone file
  return text

-- Sixteen nested divisions, sixteen nested modulos and a sixteen-deep mix of the two. The
-- level below is the dividend at even levels and the divisor at odd levels, so both
-- operand positions nest. The zero test uses the dividend twice and the divisor three
-- times; the text stays small all the same, since an operand that is long is written once.
#guard_msgs in
run_elab do
  let ctx : Core.SMT.Context := { ufs := .ofArray #[x, y] }
  let nest (ops : List Strata.SMT.Op) : Strata.SMT.Term :=
    ops.zipIdx.foldl (fun t (op, i) =>
      if i % 2 == 0 then .app op [t, call y] .int else .app op [xTerm, t] .int) xTerm
  let cases : List (String × List Strata.SMT.Op × Nat × Nat) := [
    ("nested divisions", List.replicate 16 .div, 16, 0),
    ("nested modulos", List.replicate 16 .mod, 0, 16),
    ("nested divisions and modulos",
      (List.range 16).map (fun i => if i % 3 == 0 then .mod else .div), 10, 6)]
  for (name, ops, divisions, modulos) in cases do
    let _ ← dividedExport name divisions modulos (.app .eq [nest ops, .int 0] .bool) (ctx := ctx)

-- Division under a quantifier: the bound variable is the dividend in one division and the
-- divisor in another, under a universal and an existential quantifier. A quantified
-- variable named like one of the translator's binders is another variable in the file.
#guard_msgs in
run_elab do
  let ctx : Core.SMT.Context := { ufs := .ofArray #[x, y] }
  let v : TermVar := ⟨"v", .int⟩
  let w : TermVar := ⟨"w", .int⟩
  let body : Strata.SMT.Term := .app .le [.app .div [.var v, call y] .int,
    .app .mod [xTerm, .var v] .int] .bool
  let text ← dividedExport "division under a quantifier" 2 1 (ctx := ctx)
    (.quant .all [v] [] (.app .or [body, .quant .exist [w] []
      (.app .eq [.app .div [.var w, .var v] .int, xTerm] .bool)] .bool))
  unless has text "∀ («v» : @Int)," do
    throwError "the quantified variable is not bound in the exported proposition: {text}"
  for name in ["divByZero", "modByZero"] do
    let bound : TermVar := ⟨name, .int⟩
    let _ ← dividedExport s!"quantified variable named {name}" 1 1 (ctx := ctx)
      (.quant .all [bound] [] (.app .le [.app .div [.var bound, call y] .int,
        .app .mod [xTerm, .var bound] .int] .bool))

-- Division in one premise only: an assumption divides, or an axiom takes a modulo, and
-- nothing else of the query does.
#guard_msgs in
run_elab do
  let goal : Strata.SMT.Term := .app .le [xTerm, xTerm] .bool
  let _ ← dividedExport "division in an assumption" 1 0 goal (ctx := { ufs := .ofArray #[x, y] })
    (assumptions := [.app .le [.int 0, .app .div [xTerm, call y] .int] .bool])
  let _ ← dividedExport "modulo in an axiom" 0 1 goal (ctx := {
    ufs := .ofArray #[x, y]
    axms := .ofArray #[.app .le [.int 0, .app .mod [xTerm, call y] .int] .bool] })

-- Division in the definitions of the context only (the functions of a program): the goal
-- applies two of them.
#guard_msgs in
run_elab do
  let a : TermVar := ⟨"a", .int⟩
  let b : TermVar := ⟨"b", .int⟩
  let ratio : Strata.SMT.IF := {
    id := "ratio", args := [a, b], out := .int, body := .app .div [.var a, .var b] .int }
  let rest : Strata.SMT.IF := {
    id := "rest", args := [a, b], out := .int, body := .app .mod [.var a, .var b] .int }
  let _ ← dividedExport "division in context definitions" 1 1
    (ctx := { ufs := .ofArray #[x, y], ifs := .ofArray #[ratio, rest] })
    (.app .le [.app (.uf ratio.toUF) [xTerm, call y] .int,
      .app (.uf rest.toUF) [xTerm, call y] .int] .bool)

-- Division inside definition bodies: a definition divides, a later one divides by the
-- first, and a definition with parameters divides one by the other.
#guard_msgs in
run_elab do
  let q := intVar "q"
  let r := intVar "r"
  let a : TermVar := ⟨"a", .int⟩
  let b : TermVar := ⟨"b", .int⟩
  let ratio : Strata.SMT.IF := {
    id := "ratio", args := [a, b], out := .int, body := .app .div [.var a, .var b] .int }
  let definitions : List Core.VarDefinition := [
    { name := "q", ty := .int, body := .app .div [xTerm, call y] .int },
    { name := "r", ty := .int, body := .app .mod [call y, call q] .int }]
  let _ ← dividedExport "division in definitions" 2 1 (definitions := definitions)
    (ctx := { ufs := .ofArray #[x, y], ifs := .ofArray #[ratio] })
    (.app .le [.app .add [call r, .app (.uf ratio.toUF) [xTerm, call q] .int] .int, xTerm] .bool)

-- The query's own symbols are named like the translator's binders: a variable `divByZero`
-- and a function `modByZero`. They are declared after the binders, with a suffix.
#guard_msgs in
run_elab do
  let own := intVar "divByZero"
  let f : UF := { id := "modByZero", args := [.int], out := .int }
  let text ← dividedExport "the binders' names taken" 1 1 (ctx := { ufs := .ofArray #[own, f] })
    (.app .eq [.app .mod [.app .div [.app (.uf f) [call own] .int, call own] .int, call own] .int,
      call own] .bool)
  for binder in ["∀ («divByZero» : (@Int →", "∀ («modByZero» : (@Int →",
      "∀ («divByZero_1» : @Int),", "∀ («modByZero_1» : (@Int →"] do
    unless occurrences text binder == 1 do
      throwError "`{binder}` does not occur once: {text}"

-- A query without division or modulo has no binder for a value at zero.
#guard_msgs in
run_elab do
  let _ ← dividedExport "no division" 0 0 (ctx := { ufs := .ofArray #[x] })
    (.app .le [.app .add [xTerm, .int 1] .int, .app .mul [xTerm, .int 2] .int] .bool)

-- `5 div 0 = 0` holds in Lean's arithmetic and is open in SMT-LIB's. The file states a
-- proposition that is false, and Lean refutes it with the function that is 1 everywhere.
#guard_msgs in
run_elab do
  let text ← dividedExport "division by the literal zero" 1 0
    (.app .eq [.app .div [.int 5, .int 0] .int, .int 0] .bool)
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let file := dir / "Refuted.lean"
    IO.FS.writeFile file (text ++ "\nexample : ¬ vcProp :=\n  \
      fun h => absurd (h (fun _ => 1) (fun _ => 1)) (by decide)\n")
    compilesAlone file

/-! A term that uses a subterm several times is written with that subterm bound once: the
operand of `abs` (four uses in its translation), an operand used in the condition and in a
branch of an `if`, the middle operand of a chained equality. Nesting such terms does not
multiply the text. -/
#guard_msgs in
run_elab do
  let ctx : Core.SMT.Context := { ufs := .ofArray #[x, y] }
  let absolute (n : Nat) := (List.range n).foldl
    (fun (t : Strata.SMT.Term) _ => .app .abs [t] .int) xTerm
  let smaller (n : Nat) := (List.range n).foldl (fun (t : Strata.SMT.Term) _ =>
    .app .ite [.app .lt [t, call y] .bool, t, call y] .int) xTerm
  -- Read back, with the bindings unfolded, they are the expressions they were printed from.
  let (text, _) ← readsBackIdentical "nested abs" (ctx := ctx) (.app .le [.int 0, absolute 6] .bool)
  unless has text "let «_s1» := " do
    throwError "the operand of a nested `abs` is not bound once: {text}"
  let _ ← readsBackIdentical "nested if" (ctx := ctx) (.app .le [smaller 8, xTerm] .bool)
  let _ ← readsBackIdentical "nested chain" (ctx := { ufs := .ofArray #[p] }) (chained 8)
  -- A generated name avoids a symbol of the query that has it.
  let named := intVar "_s1"
  let (text, _) ← readsBackIdentical "a symbol named like a binding"
    (ctx := { ufs := .ofArray #[x, named] })
    (.app .le [call named, .app .abs [.app .abs [.app .abs [xTerm] .int] .int] .int] .bool)
  unless has text "let «_s1_1» := " do
    throwError "a binding took the name of a symbol in scope: {text}"
  -- Thirty levels stay small and compile; written out, they would be 4³⁰ operands. The
  -- bindings are part of the text a file may hold: the proposition is refused under a limit
  -- of 10000 bytes, and written with its bindings under one of 20000.
  let deep : Strata.SMT.Term := .app .le [.int 0, absolute 30] .bool
  expectRefused "too large to write" deep (ctx := ctx)
    (configure := fun config => { config with maxFileBytes := 10000 })
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let config : ExportConfig := { directory := dir, maxFileBytes := 20000 }
    config.exportValidity .unknown ctx [] deep [] [] "abs"
    config.exportValidity .unknown ctx [] (.app .le [smaller 10, xTerm] .bool) [] [] "if"
    let files ← leanFiles dir
    unless files.map stem == #["abs", "if"] do
      throw <| IO.userError "The nested terms were not both exported"
    for file in files do
      unless has (← IO.FS.readFile file) "let «_s" do
        throw <| IO.userError s!"{file}: a repeated subterm is not bound"
      compilesAlone file

/-! Two limits refuse a query that is too large: one on the size of the normalized query,
checked before the passes that walk it as a tree, and one on the text. Either way the check
writes no file and says why. -/
#guard_msgs in
run_elab do
  let ctx : Core.SMT.Context := { ufs := .ofArray #[x] }
  let goal : Strata.SMT.Term := .app .eq [xTerm, xTerm] .bool
  expectRefused "too large to export" (chained 60) (ctx := { ufs := .ofArray #[p] })
  expectRefused "too large to write" goal (ctx := ctx)
    (configure := fun config => { config with maxFileBytes := 20 })
  -- The default limit admits the same query.
  let _ ← exportOne goal (ctx := ctx)

/-! Publication never replaces a file: one that appears after the export looked for it, while
the text was being written, is kept, and the export reports `kept`. A file appears under its
name complete or not at all: a publication that fails leaves nothing there. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun dir => do
    let staged := dir / ".staged.tmp"
    let file := dir / "vc.lean"
    IO.FS.writeFile staged "exported"
    IO.FS.writeFile file "a proof saved in the meantime"
    unless !(← publish staged file) && (← IO.FS.readFile file) == "a proof saved in the meantime" &&
        !(← staged.pathExists) do
      throw <| IO.userError "Publication replaced an existing file or left its staged file"
    let fresh := dir / "fresh.lean"
    IO.FS.writeFile staged "exported"
    unless (← publish staged fresh) && (← IO.FS.readFile fresh) == "exported" &&
        !(← staged.pathExists) do
      throw <| IO.userError "Publication did not move the staged file to a free name"
    -- A failed publication (here: nothing staged) leaves no file, so a later run exports it.
    let failed := dir / "failed.lean"
    let threw ← try let _ ← publish (dir / ".missing.tmp") failed; pure false catch _ => pure true
    unless threw && !(← failed.pathExists) do
      throw <| IO.userError "A failed publication left a file under the final name"

/-! Three large queries. A long conjunction, and an `if` whose condition is quantified and
stands in the instance of the `if` as well, are written in text that grows with their size
and no faster. A term whose shared subterms make it enormous written out is refused before
any pass walks it. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    let ctx : Core.SMT.Context := { ufs := .ofArray #[x, p] }
    let v : TermVar := ⟨"v", .int⟩
    let long : Strata.SMT.Term :=
      .app .and ((List.range 4000).map fun (i : Nat) => .app .le [.int i, xTerm] .bool) .bool
    -- Each level's condition is a quantification over the level below.
    let quantified := (List.range 40).foldl (fun (t : Strata.SMT.Term) (i : Nat) =>
      .app .ite [.quant .all [v] [] (.app .or [t, .app .le [.var v, .int i] .bool] .bool),
        call p, .app .le [.int i, xTerm] .bool] .bool) (call p)
    -- The level below is used three times at every level: 3²⁰⁰ nodes written out.
    let shared := (List.range 200).foldl (fun (t : Strata.SMT.Term) _ =>
      .app .ite [.app .lt [t, xTerm] .bool, t, .app .add [t, .int 1] .int] .int) xTerm
    for (name, query, bytes) in [("long", long, 600000), ("quantified", quantified, 200000)] do
      let (config, events) ← recording (root / name)
      config.exportValidity .unknown ctx [] query [] [] name
      let files ← leanFiles (root / name)
      let texts ← files.mapM IO.FS.readFile
      unless files.map stem == #[name] && texts.all (·.utf8ByteSize < bytes) do
        throw <| IO.userError s!"{name}: not exported within {bytes} bytes: \
          {(← events.get).map fun e => (e.stage, e.diagnostic)}"
    expectRefused "too large to export" (.app .le [shared, xTerm] .bool) (ctx := ctx)

-- The size bound counts what normalization writes, no more: a two-operand `distinct` writes
-- each operand once, and a chain writes its end operands once. Nesting through those places
-- stays linear and is exported.
#guard_msgs in
run_elab do
  let nestedDistinct := (List.range 20).foldl
    (fun (t : Strata.SMT.Term) _ => .app .distinct [t, .bool false] .bool) (.bool true)
  let _ ← readsBackIdentical "nested binary distinct" nestedDistinct
  let throughEnd := (List.range 20).foldl
    (fun (t : Strata.SMT.Term) _ => .app .eq [t, call p, call p] .bool) (call p)
  let _ ← readsBackIdentical "chain nested through an end" (ctx := { ufs := .ofArray #[p] })
    throughEnd
