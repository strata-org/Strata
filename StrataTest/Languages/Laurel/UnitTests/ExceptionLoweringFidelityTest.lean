/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
Three things the exceptional lowering must not silently change about the program it
was handed. None of them is reachable through the grammar, so all three are built
directly as ASTs — which is also how they became reachable in the first place:
`ThrowsOnBlock` is public AST and front ends construct Laurel programs rather than
parsing them.

1. An authored `Condition.mode` on a case's `ensures` survives the rewrite. The
   surface has no `free`/`checked` form for a case, so every *parsed* case
   postcondition is `Both`; a front end that sets `.Assume` directly must get an
   assumption, not a checked obligation, or it verifies against a contract nobody
   wrote.
2. A wildcard case frame means "may change anything", so it must contribute no
   frame. Reaching the frame builder it would arrive as an empty entry list, which
   encodes "nothing changed" — the inverse — and on a bodiless procedure that is
   assumed rather than checked.
3. A shape the pass rejects must be returned unchanged. Lowering it anyway yields
   `Result<bool, T>` with a placeholder payload and no real outputs, and the erasure
   backstop must not then report the pass's own deliberate no-op as an internal bug.
-/

meta import Strata.Languages.Laurel.EliminateExceptions
meta import Strata.Languages.Laurel.ModifiesClauses

meta section

open Strata
open Strata.Laurel

private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := .unknown }

private def call (name : String) : StmtExprMd :=
  ⟨.StaticCall (mkId name) [], .unknown⟩

private def emptyModel : SemanticModel :=
  { nextId := 0, compositeCount := 0, refToDef := {} }

private def modeName : ConditionMode → String
  | .Assert => "Assert"
  | .Assume => "Assume"
  | .Both   => "Both"

/-! ## 1. An authored case-postcondition mode survives lowering -/

/-- A throwing procedure *with a body*, whose single case postcondition is authored
    `.Assume`. With a body the pass computes `.Both` for everything it synthesizes, so
    this is exactly the case where an overwrite is observable. -/
private def authoredAssume : Program :=
  { staticProcedures := [
      { name := mkId "assumeOnly"
        inputs := []
        outputs := []
        preconditions := []
        decreases := none
        throwsType := some (mkTy (.UserDefined (mkId "Err")))
        throwsBinding := some (mkId "e")
        throwsOn := [
          { guard := call "g"
            postconditions := [{ condition := call "p", mode := .Assume }]
            modifies := [] }
        ]
        body := .Transparent ⟨.Block [] none, .unknown⟩ }
    ]
    staticFields := []
    types := [] }

-- The emitted postconditions, in order, are: the derived `isBad ==> err is T` (no
-- summary), the case's forcing claim, then the authored `ensures`. Only the last is
-- authored, so only the last should carry a mode the pass did not compute.
/-- info: modes in order: Both, Both, Assume
authored ensures (last): Assume -/
#guard_msgs in
#eval do
  let (prog, _) := eliminateExceptionsTransform emptyModel authoredAssume
  match prog.staticProcedures with
  | [p] =>
    match p.body with
    | .Opaque posts _ _ =>
      IO.println s!"modes in order: {", ".intercalate (posts.map (fun (c : Condition) => modeName c.mode))}"
      match posts.reverse with
      | authored :: _ => IO.println s!"authored ensures (last): {modeName authored.mode}"
      | [] => IO.println "no postconditions emitted"
    | _ => IO.println "unexpected body kind"
  | ps => IO.println s!"unexpected procedure count: {ps.length}"

/-! ## 2. A wildcard case frame contributes no frame -/

private def blockWith (mods : List StmtExprMd) : ThrowsOnBlock :=
  { guard := call "g", postconditions := [], modifies := mods }

/-- info: no targets: false
one named target: true
wildcard alone: false
wildcard beside a named target: false -/
#guard_msgs in
#eval do
  let wildcard : StmtExprMd := ⟨.All, .unknown⟩
  IO.println s!"no targets: {caseContributesFrame (blockWith [])}"
  IO.println s!"one named target: {caseContributesFrame (blockWith [call "logCell"])}"
  IO.println s!"wildcard alone: {caseContributesFrame (blockWith [wildcard])}"
  IO.println s!"wildcard beside a named target: {caseContributesFrame (blockWith [wildcard, call "logCell"])}"

/-! ## 3. A rejected shape is left unlowered, with no backstop cascade -/

/-- A throwing procedure with two value outputs: unsupported, because the lowering
    packs a procedure's outcomes into one `Result`. -/
private def twoValueOutputs : Program :=
  { staticProcedures := [
      { name := mkId "twoOut"
        inputs := []
        outputs := [{ name := mkId "a", type := mkTy .TInt },
                    { name := mkId "b", type := mkTy .TInt }]
        preconditions := []
        decreases := none
        throwsType := some (mkTy (.UserDefined (mkId "Err")))
        throwsBinding := some (mkId "e")
        throwsOn := []
        body := .Transparent ⟨.Block [] none, .unknown⟩ }
    ]
    staticFields := []
    types := [] }

/-- info: diagnostics: 1
  notYetImplemented (StrataBug: false)
outputs kept: a, b
throwsType still present: true -/
#guard_msgs in
#eval do
  let (prog, diags) := eliminateExceptionsTransform emptyModel twoValueOutputs
  IO.println s!"diagnostics: {diags.length}"
  diags.forM fun (d : Message) => do
    let isBug := d.kind == MessageKind.strataBug
    IO.println s!"  {d.kind} (StrataBug: {isBug})"
  match prog.staticProcedures with
  | [p] =>
    IO.println s!"outputs kept: {", ".intercalate (p.outputs.map (fun (o : Parameter) => o.name.text))}"
    IO.println s!"throwsType still present: {p.throwsType.isSome}"
  | ps => IO.println s!"unexpected procedure count: {ps.length}"

end
