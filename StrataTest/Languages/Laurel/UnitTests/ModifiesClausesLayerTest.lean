/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
`transformModifiesClauses` layer invariants, pinned where they live rather than
through the whole pipeline. Two families:

1. *Group disposition.* An empty-target group is the opaque default "nothing
   changes" frame and must be KEPT; a wildcard-target group claims nothing and
   must be DROPPED; and zero groups mean unframed. A mutation that treats empty
   groups like wildcards would silently unframe every defaulted opaque
   procedure — the e2e suites only catch that incidentally.

2. *The enumerated-frame split under a guard.* With the optimization on, a
   group whose targets are individual references lowers to the assume/assert
   pair (callers get the quantifier-free enumerated frame, the body checks the
   quantified one) — for unguarded AND guarded groups alike, both halves under
   the group's guard. Gating the split on unguarded groups would silently make
   every lowered throwing procedure's normal frame quantified for callers, a
   precision/perf regression invisible to soundness-only tests.

Procedures are built directly as ASTs: the layer under test runs after heap
parameterization, whose output shape (a `$heap` output, resolved targets) is
easiest to state explicitly.
-/

meta import Strata.Languages.Laurel.ModifiesClauses

meta section

open Strata
open Strata.Laurel

private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := .unknown }

/-- A resolved reference to the composite parameter `c` (uniqueId 1). -/
private def cRef : StmtExprMd :=
  ⟨.Var (.Local { text := "c", uniqueId := some 1 }), .unknown⟩

/-- A model that knows two things: `c` is a composite (all
    `extractModifiesEntries` needs to classify `cRef` as an individual ref), and
    the procedure under test writes the heap — which is what the transform asks,
    rather than inspecting the signature. -/
private def cModel : SemanticModel :=
  { nextId := 3, compositeCount := 1,
    refToDef := ({} : Std.HashMap Nat ResolvedNode).insert 1
      (.var { text := "c", uniqueId := some 1 } (mkTy (.UserDefined (mkId "Cell")))),
    heapWriters := ({} : Std.HashSet Nat).insert 2 }

/-- An opaque heap-writing procedure carrying the given modifies groups. The
    `$heap` output mirrors what heap parameterization leaves, but what marks it a
    heap writer is `cModel.heapWriters` (uniqueId 2) — that is what the transform
    consults. -/
private def procWithGroups (groups : List ModifiesGroup)
    (bodiless : Bool := false) : Procedure :=
  { name := { text := "p", uniqueId := some 2 }
    inputs := []
    outputs := [{ name := mkId "$heap", type := mkTy (.UserDefined (mkId "Heap")) }]
    preconditions := []
    decreases := none
    throwsType := none
    throwsBinding := none
    throwsOn := []
    body := .Opaque [] (if bodiless then none else some ⟨.Block [] none, .unknown⟩) groups }

/-- The frame conditions the transform attached (the test procedures start with
    zero postconditions, so every postcondition is a frame condition). -/
private def framesOf (groups : List ModifiesGroup) (useEnumeratedFrame : Bool)
    (bodiless : Bool := false) : List Condition :=
  match transformModifiesClauses cModel (procWithGroups groups bodiless) useEnumeratedFrame with
  | .ok p => match p.body with
    | .Opaque posts _ _ => posts
    | _ => []
  | .error _ => []

private def modeName : ConditionMode → String
  | .Assert => "Assert"
  | .Assume => "Assume"
  | .Both   => "Both"

private partial def containsQuantifier (e : StmtExprMd) : Bool :=
  match e.val with
  | .Quantifier .. => true
  | .StaticCall _ args => args.any containsQuantifier
  | _ => false

private def isImpliesWrapped (e : StmtExprMd) : Bool :=
  match e.val with
  | .StaticCall n (_ :: _ :: _) => n.text == Operation.Implies.procName
  | _ => false

/-- One line per condition: mode, whether the group's guard survived as an
    implication wrapper, and whether the frame is the quantified form. -/
private def describe (cs : List Condition) : String :=
  if cs.isEmpty then "(no conditions)"
  else "\n".intercalate (cs.map fun c =>
    s!"{modeName c.mode}, guarded={isImpliesWrapped c.condition}, quantified={containsQuantifier c.condition}")

private def guard? : Option StmtExprMd := some ⟨.StaticCall (mkId "isGood") [], .unknown⟩

/-! ## 1. Group disposition: empty kept, wildcard dropped, absent unframed -/

/--
info: zero groups: (no conditions)
empty group: Both, guarded=false, quantified=true
wildcard group: (no conditions)
wildcard beside named target: (no conditions)
-/
#guard_msgs in
#eval do
  IO.println s!"zero groups: {describe (framesOf [] false)}"
  IO.println s!"empty group: {describe (framesOf [{ targets := [] }] false)}"
  IO.println s!"wildcard group: {describe (framesOf [{ targets := [⟨.All, .unknown⟩] }] false)}"
  IO.println s!"wildcard beside named target: {describe (framesOf [{ targets := [⟨.All, .unknown⟩, cRef] }] false)}"

/-! ## 2. The enumerated split applies under a guard -/

/--
info: unguarded, enumerated on:
Assume, guarded=false, quantified=false
Assert, guarded=false, quantified=true
guarded, enumerated on:
Assume, guarded=true, quantified=false
Assert, guarded=true, quantified=true
guarded, enumerated off:
Both, guarded=true, quantified=true
empty targets take the plain form (no split):
Both, guarded=false, quantified=true
-/
#guard_msgs in
#eval do
  IO.println s!"unguarded, enumerated on:\n{describe (framesOf [{ targets := [cRef] }] true)}"
  IO.println s!"guarded, enumerated on:\n{describe (framesOf [{ targets := [cRef], guard := guard? }] true)}"
  IO.println s!"guarded, enumerated off:\n{describe (framesOf [{ targets := [cRef], guard := guard? }] false)}"
  IO.println s!"empty targets take the plain form (no split):\n{describe (framesOf [{ targets := [] }] true)}"

/-! ## 3. The plain form's mode: checked with a body, assumed without one -/

/--
info: with body: Both
bodiless: Assume
-/
#guard_msgs in
#eval do
  let mode (bodiless : Bool) :=
    match framesOf [{ targets := [cRef], guard := guard? }] false bodiless with
    | [c] => modeName c.mode
    | cs => s!"unexpected condition count: {cs.length}"
  IO.println s!"with body: {mode false}"
  IO.println s!"bodiless: {mode true}"

end
