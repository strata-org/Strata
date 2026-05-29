/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.DDMTransform.Translate
meta import Strata.DDM.Elab

meta section

/-! ## Tests for SMT DDM Translate -/

open StrataDDM (Decimal)

namespace Strata.SMTDDM

/-- info: Except.ok "(+ 10 20)" -/
#guard_msgs in #eval (termToString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int 20))] .int))

/-- info: Except.ok "(+ 10 (- 20))" -/
#guard_msgs in #eval (termToString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int (-20)))] .int))

/-- info: Except.ok "(+ 0.1 0.02)" -/
#guard_msgs in #eval (termToString
    (.app SMT.Op.add [(.prim (.real (Decimal.mk 1 (-1)))),
                      (.prim (.real (Decimal.mk 2 (-2))))] .int))

/-- info: Except.ok "0.01" -/
#guard_msgs in #eval (termToString (.prim (.real (Decimal.mk 1 (-2)))))

/-- info: Except.ok "0.005" -/
#guard_msgs in #eval (termToString (.prim (.real (Decimal.mk 5 (-3)))))

/-- info: Except.ok "0.001" -/
#guard_msgs in #eval (termToString (.prim (.real (Decimal.mk 1 (-3)))))

/-- info: Except.ok "(_ bv1 32)" -/
#guard_msgs in #eval (termToString
    (.prim (.bitvec (BitVec.ofNat 32/-width-/ 1/-value-/))))

-- Test: bitvec literal inside a quantifier trigger pattern (exercises termToSExpr
-- with an indexed identifier, which previously failed).
/-- info: Except.ok "(forall ((a (_ BitVec 32))) (! (= (bvand a (_ bv0 32)) (_ bv0 32)) :pattern ((bvand a (_ bv0 32)))))" -/
#guard_msgs in #eval (termToString
    (let bv32 : SMT.TermType := .prim (.bitvec 32)
     let a : SMT.Term := .app (.uf { id := "a", args := [], out := bv32 }) [] bv32
     let bv0 : SMT.Term := .prim (.bitvec (BitVec.ofNat 32 0))
     let abv0 : SMT.Term := .app .bvand [a, bv0] bv32
     let body : SMT.Term := .app .eq [abv0, bv0] (.prim .bool)
     let trigger : SMT.Term := .app .triggers [.app .triggers [abv0] .trigger] .trigger
     .quant .all [⟨"a", bv32⟩] trigger body))

end Strata.SMTDDM

/-! ## Tests for bitvec literal decoding in translateFromDDMTermToUntyped -/

namespace Strata.SMTResponseDDM

/-- Helper: parse a get-value response term and decode it. -/
private def decodeTerm (s : String) : IO (Except String Strata.SMT.Term) := do
  let inputCtx := Strata.Parser.stringInputContext "test" s
  let op ←
    try pure (some (← Strata.Elab.parseCategoryFromDialect
          smtResponseDialects q`SMTCore.Term inputCtx))
    catch _ => pure none
  match op with
  | none => return .error "parse failed"
  | some ast =>
    match Term.ofAst ast with
    | .ok t => return translateFromDDMTermToUntyped t
    | .error e => return .error s!"ofAst failed: {e}"

-- Decoding `(_ bv5 32)` yields `BitVec.ofNat 32 5`
/-- info: Except.ok (Strata.SMT.Term.prim (Strata.SMT.TermPrim.bitvec 0x00000005#32)) -/
#guard_msgs in #eval decodeTerm "(_ bv5 32)"

/-- info: Except.ok (Strata.SMT.Term.prim (Strata.SMT.TermPrim.bitvec 0xff#8)) -/
#guard_msgs in #eval decodeTerm "(_ bv255 8)"

/-- info: Except.ok (Strata.SMT.Term.prim (Strata.SMT.TermPrim.bitvec 0x0000000000000000#64)) -/
#guard_msgs in #eval decodeTerm "(_ bv0 64)"

end Strata.SMTResponseDDM

end
