/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
# Tests for the proof-producing SMT translation

For one query per supported construct, these tests translate the query with
`translateQuery`, prove with `Strata.SMT.ProofGen.proveQuery` that the
translation is the query's denotation, and kernel-check the resulting theorem
`denoteQuery ctx ts t = some P`. This is the check `gen_smt_vcs` performs for
each VC.
-/

open Lean (Expr mkApp mkApp2 mkApp3 addDecl Declaration logInfo toExpr getEnv)
open Lean.Meta
open Strata Strata.SMT

namespace Strata.DenoteProofTests
abbrev B := TermType.prim .bool
abbrev I := TermType.prim .int
abbrev S := TermType.prim .string
def BV (n : Nat) : TermType := .prim (.bitvec n)
def c (n : String) (ty : TermType) : SMT.Term := .app (.uf ⟨n, [], ty⟩) [] ty
def ap (o : Op) (as : List SMT.Term) (ty : TermType) : SMT.Term := .app o as ty
def bv (n : Nat) (k : Nat) : SMT.Term := .prim (.bitvec (BitVec.ofNat n k))
def eq (a b : SMT.Term) : SMT.Term := ap .eq [a, b] B
def ctxOf (ufs : List UF) (sorts : List Strata.DL.SMT.Sort := []) (tySubst : Map String TermType := [])
    (ifs : List IF := []) (axms : List SMT.Term := []) : SanitizedContext :=
  { ufs := ufs.toArray, sorts := sorts.toArray, tySubst, ifs := ifs.toArray, axms := axms.toArray }
def x8 := c "x" (BV 8)
def y8 := c "y" (BV 8)
def u8 : List UF := [⟨"x", [], BV 8⟩, ⟨"y", [], BV 8⟩]
def Arr := TermType.constr "Array" [I, I]
def v (n : String) (ty : TermType) : SMT.Term := .var ⟨n, ty⟩
def f1 (n : String) (a : SMT.Term) (aTy ty : TermType) : SMT.Term := .app (.uf ⟨n, [aTy], ty⟩) [a] ty
-- Parameterized uninterpreted sorts `T α` and `P α β`.
def TI := TermType.constr "T" [I]
def PTB := TermType.constr "P" [TI, B]
def MyInt := TermType.constr "MyInt" []
def n := c "n" I
def m := c "m" I
def b := c "b" B
def uIB : List UF := [⟨"n", [], I⟩, ⟨"m", [], I⟩, ⟨"b", [], B⟩]

def cases : List (String × SanitizedContext × List SMT.Term × SMT.Term) := [
  ("bvlit", ctxOf [], [], eq (bv 8 3) (bv 8 3)),
  ("bvneg", ctxOf u8, [], eq (ap .bvneg [x8] (BV 8)) y8),
  ("bvnot", ctxOf u8, [], eq (ap .bvnot [x8] (BV 8)) y8),
  ("bvnego", ctxOf u8, [], ap .bvnego [x8] B),
  ("bvadd3", ctxOf u8, [], eq (ap .bvadd [x8, y8, x8] (BV 8)) y8),
  ("bvsub", ctxOf u8, [], eq (ap .bvsub [x8, y8] (BV 8)) y8),
  ("bvmul", ctxOf u8, [], eq (ap .bvmul [x8, y8] (BV 8)) y8),
  ("bvand", ctxOf u8, [], eq (ap .bvand [x8, y8] (BV 8)) y8),
  ("bvor", ctxOf u8, [], eq (ap .bvor [x8, y8] (BV 8)) y8),
  ("bvxor", ctxOf u8, [], eq (ap .bvxor [x8, y8] (BV 8)) y8),
  ("bvshl", ctxOf u8, [], eq (ap .bvshl [x8, y8] (BV 8)) y8),
  ("bvlshr", ctxOf u8, [], eq (ap .bvlshr [x8, y8] (BV 8)) y8),
  ("bvashr", ctxOf u8, [], eq (ap .bvashr [x8, y8] (BV 8)) y8),
  ("bvslt", ctxOf u8, [], ap .bvslt [x8, y8] B),
  ("bvsle", ctxOf u8, [], ap .bvsle [x8, y8] B),
  ("bvult", ctxOf u8, [], ap .bvult [x8, y8] B),
  ("bvsge", ctxOf u8, [], ap .bvsge [x8, y8] B),
  ("bvsgt", ctxOf u8, [], ap .bvsgt [x8, y8] B),
  ("bvule", ctxOf u8, [], ap .bvule [x8, y8] B),
  ("bvugt", ctxOf u8, [], ap .bvugt [x8, y8] B),
  ("bvuge", ctxOf u8, [], ap .bvuge [x8, y8] B),
  ("bvudiv", ctxOf u8, [], eq (ap .bvudiv [x8, y8] (BV 8)) y8),
  ("bvurem", ctxOf u8, [], eq (ap .bvurem [x8, y8] (BV 8)) y8),
  ("bvsdiv", ctxOf u8, [], eq (ap .bvsdiv [x8, y8] (BV 8)) y8),
  ("bvsrem", ctxOf u8, [], eq (ap .bvsrem [x8, y8] (BV 8)) y8),
  ("bvsaddo", ctxOf u8, [], ap .bvsaddo [x8, y8] B),
  ("bvssubo", ctxOf u8, [], ap .bvssubo [x8, y8] B),
  ("bvsmulo", ctxOf u8, [], ap .bvsmulo [x8, y8] B),
  ("bvconcat", ctxOf u8, [], eq (ap .bvconcat [x8, y8] (BV 16)) (ap .bvconcat [y8, x8] (BV 16))),
  ("zero_extend", ctxOf u8, [], eq (ap (.zero_extend 8) [x8] (BV 16)) (ap (.zero_extend 8) [y8] (BV 16))),
  ("ubv_to_int", ctxOf u8, [], ap .le [ap .ubv_to_int [x8] I, .prim (.int 255)] B),
  ("sbv_to_int", ctxOf u8, [], ap .le [ap .sbv_to_int [x8] I, .prim (.int 127)] B),
  ("int_to_bv", ctxOf (u8 ++ [⟨"n", [], I⟩]), [], eq (ap (.int_to_bv 8) [c "n" I] (BV 8)) x8),
  ("bvquant", ctxOf u8, [], .quant .all [⟨"z", BV 8⟩] [] (eq (ap .bvadd [.var ⟨"z", BV 8⟩, x8] (BV 8)) y8)),
  ("strlit", ctxOf [⟨"s", [], S⟩], [], eq (c "s" S) (.prim (.string "hello"))),
  ("strlen", ctxOf [⟨"s", [], S⟩], [], ap .ge [ap .str_length [c "s" S] I, .prim (.int 0)] B),
  ("strconcat", ctxOf [⟨"s", [], S⟩], [], eq (ap .str_concat [c "s" S, .prim (.string "a"), c "s" S] S) (c "s" S)),
  ("select", ctxOf [⟨"a", [], Arr⟩], [], eq (ap .select [c "a" Arr, .prim (.int 1)] I) (.prim (.int 2))),
  ("store", ctxOf [⟨"a", [], Arr⟩], [],
    eq (ap .select [ap .store [c "a" Arr, .prim (.int 1), .prim (.int 2)] Arr, .prim (.int 1)] I) (.prim (.int 2))),
  ("arrayfun", ctxOf [⟨"a", [], Arr⟩, ⟨"g", [Arr], I⟩], [],
    eq (.app (.uf ⟨"g", [Arr], I⟩) [ap .store [c "a" Arr, .prim (.int 1), .prim (.int 2)] Arr] I) (.prim (.int 0))),
  ("none", ctxOf [⟨"o", [], .option I⟩], [], eq (c "o" (.option I)) (.none I)),
  ("some", ctxOf [⟨"o", [], .option I⟩], [], eq (c "o" (.option I)) (.some (.prim (.int 3)))),
  ("abs", ctxOf [⟨"n", [], I⟩], [], ap .ge [ap .abs [c "n" I] I, .prim (.int 0)] B),
  ("synonym", ctxOf [⟨"m", [], .constr "MyInt" []⟩] [] [("MyInt", I)], [],
    ap .ge [c "m" (.constr "MyInt" []), .prim (.int 0)] B),
  ("synonym_sort", ctxOf [⟨"p", [], .constr "P" []⟩, ⟨"q", [], .constr "P" []⟩] [⟨"T", 0⟩] [("P", .constr "T" [])], [],
    eq (c "p" (.constr "P" [])) (c "q" (.constr "P" []))),
  ("synonym_bv", ctxOf [⟨"w", [], .constr "Word" []⟩] [] [("Word", BV 8)], [],
    eq (ap .bvadd [c "w" (.constr "Word" []), bv 8 1] (BV 8)) (c "w" (.constr "Word" []))),
  -- Declarations that share a name but not a type: the lookup in `denoteTerm`
  -- compares the whole declaration, so it skips the inner `x : Bool` (resp.
  -- `f : Bool → Bool`) when resolving `x : Int` (resp. `f : Int → Int`).
  ("shadow_var", ctxOf [], [],
    .quant .all [⟨"x", I⟩] [] (.quant .all [⟨"x", B⟩] [] (ap .ge [.var ⟨"x", I⟩, .prim (.int 0)] B))),
  ("overload_uf", ctxOf [⟨"f", [I], I⟩, ⟨"f", [B], B⟩], [],
    ap .and [ap .ge [.app (.uf ⟨"f", [I], I⟩) [.prim (.int 1)] I, .prim (.int 0)] B,
             .app (.uf ⟨"f", [B], B⟩) [.prim (.bool true)] B] B),
  -- Uninterpreted sorts of arity > 0 (`bindUSs_cons` with `mkNonemptyPred`).
  ("sort_arity1", ctxOf [⟨"p", [], TI⟩, ⟨"q", [], TI⟩] [⟨"T", 1⟩], [], eq (c "p" TI) (c "q" TI)),
  ("sort_arity2", ctxOf [⟨"p", [], PTB⟩, ⟨"g", [PTB], I⟩] [⟨"T", 1⟩, ⟨"P", 2⟩], [],
    ap .ge [f1 "g" (c "p" PTB) PTB I, .prim (.int 0)] B),
  ("sort_arity1_quant", ctxOf [⟨"g", [TI], I⟩] [⟨"T", 1⟩], [],
    .quant .all [⟨"x", TI⟩] [] (eq (f1 "g" (v "x" TI) TI I) (f1 "g" (v "x" TI) TI I))),
  -- A sort synonym used in the signature and body of an interpreted function.
  ("synonym_if", ctxOf [⟨"m", [], MyInt⟩] [] [("MyInt", I)]
      [⟨"inc", [⟨"x", MyInt⟩], MyInt, ap .add [v "x" MyInt, .prim (.int 1)] MyInt, false⟩], [],
    ap .gt [f1 "inc" (c "m" MyInt) MyInt MyInt, c "m" MyInt] B),
  -- An existential inside the body of an interpreted function.
  ("exists_in_if", ctxOf [] [] []
      [⟨"hasLarger", [⟨"x", I⟩], B, .quant .exist [⟨"y", I⟩] [] (ap .gt [v "y" I, v "x" I] B), false⟩], [],
    f1 "hasLarger" (.prim (.int 0)) I B),
  -- `ite` and `=` over option and array sorts.
  ("ite_option", ctxOf [⟨"o", [], .option I⟩, ⟨"b", [], B⟩], [],
    eq (ap .ite [c "b" B, .some (.prim (.int 1)), .none I] (.option I)) (c "o" (.option I))),
  ("eq_array", ctxOf [⟨"a", [], Arr⟩, ⟨"a'", [], Arr⟩], [], eq (c "a" Arr) (c "a'" Arr)),
  ("ite_array", ctxOf [⟨"a", [], Arr⟩, ⟨"a'", [], Arr⟩, ⟨"b", [], B⟩], [],
    eq (ap .ite [c "b" B, c "a" Arr, c "a'" Arr] Arr) (c "a" Arr)),
  -- Quantifiers with non-empty triggers (one group, and two groups).
  ("trigger", ctxOf [⟨"h", [I], I⟩], [],
    .quant .all [⟨"x", I⟩] [[f1 "h" (v "x" I) I I]] (ap .ge [f1 "h" (v "x" I) I I, .prim (.int 0)] B)),
  ("trigger_groups", ctxOf [⟨"h", [I], I⟩, ⟨"k", [I], I⟩], [],
    .quant .exist [⟨"x", I⟩] [[f1 "h" (v "x" I) I I], [f1 "k" (v "x" I) I I]]
      (eq (f1 "h" (v "x" I) I I) (f1 "k" (v "x" I) I I))),
  -- Boolean and integer operators.
  ("not", ctxOf uIB, [], ap .not [b] B),
  ("or", ctxOf uIB, [], ap .or [b, ap .not [b] B, b] B),
  ("lt", ctxOf uIB, [], ap .lt [n, m] B),
  ("gt", ctxOf uIB, [], ap .gt [n, m] B),
  ("sub", ctxOf uIB, [], eq (ap .sub [n, m, n] I) m),
  ("mul", ctxOf uIB, [], eq (ap .mul [n, m] I) m),
  ("div", ctxOf uIB, [], eq (ap .div [n, .prim (.int 2)] I) m),
  ("mod", ctxOf uIB, [], eq (ap .mod [n, .prim (.int 2)] I) m),
  ("neg", ctxOf uIB, [], eq (ap .neg [n] I) m),
  ("ite_int", ctxOf uIB, [], eq (ap .ite [b, n, m] I) n),
  ("implies2", ctxOf uIB, [], ap .implies [b, b] B),
  ("implies3", ctxOf uIB, [], ap .implies [b, ap .lt [n, m] B, b] B),
  -- Assumptions and axioms, which `denoteQuery` turns into implications.
  ("assumptions", ctxOf uIB, [ap .lt [n, m] B, b], ap .le [n, m] B),
  ("axioms", ctxOf uIB [] [] [] [ap .gt [n, .prim (.int 0)] B], [ap .lt [n, m] B],
    ap .gt [m, .prim (.int 0)] B)
]
end Strata.DenoteProofTests

/-- info: 72/72 kernel-checked -/
#guard_msgs in
run_meta do
  let mut ok := 0
  for (label, sc, ts, t) in Strata.DenoteProofTests.cases do
    let (sc0, ts0, t0) := SMT.substituteSynonyms sc ts t
    match translateQuery sc0.toCore ts0 t0 with
    | .error e => logInfo m!"{label}: translateQuery failed: {e}"
    | .ok P =>
      try
        let den ← SMT.ProofGen.proveQuery sc (toExpr sc) ts (toExpr ts) t (toExpr t)
        unless (Lean.Kernel.isDefEq (← getEnv) {} den.rhs P matches .ok true) do
          throwError "denotation does not match translation"
        let ty := mkApp3 (.const ``Eq [1]) (mkApp (.const ``Option [0]) (.sort 0))
          (mkApp3 (.const ``denoteQuery []) (mkApp (.const ``Strata.SMT.SanitizedContext.toCore []) (toExpr sc)) (toExpr ts) (toExpr t))
          (mkApp2 (.const ``Option.some [0]) (.sort 0) P)
        addDecl (.thmDecl { name := `Strata.DenoteProofTests.thm ++ label.toName, levelParams := [], type := ty, value := den.proof })
        ok := ok + 1
      catch e => logInfo m!"{label}: FAIL {e.toMessageData}"
  logInfo m!"{ok}/{Strata.DenoteProofTests.cases.length} kernel-checked"

/-! `proveQuery` refuses a one-operand implication, whose denotation is `none`
(`translateQuery` reads it as its operand). -/

/-- info: proveQuery: implication needs at least two operands -/
#guard_msgs in
run_meta do
  let t : Strata.SMT.Term := .app .implies [.prim (.bool true)] (.prim .bool)
  let sc : Strata.SMT.SanitizedContext := {}
  try
    let _ ← Strata.SMT.ProofGen.proveQuery sc (toExpr sc) [] (toExpr ([] : List Strata.SMT.Term)) t (toExpr t)
    logInfo "unexpectedly proved"
  catch e => logInfo e.toMessageData

/-! `denoteQueryProof` rejects a goal that is not the query's denotation. -/

/-- info: caught: mismatch reported -/
#guard_msgs in
run_meta do
  let t : Strata.SMT.Term := .prim (.bool true)
  let sc : Strata.SMT.SanitizedContext := {}
  let wrong := Lean.mkConst ``False
  try
    let _ ← Strata.Meta.denoteQueryProof "wrong" sc (toExpr sc) [] (toExpr ([] : List Strata.SMT.Term))
      t (toExpr t) wrong
    logInfo "unexpectedly proved"
  catch e =>
    let msg ← e.toMessageData.toString
    if msg.contains "does not match the translated goal" then logInfo "caught: mismatch reported"
    else logInfo m!"unexpected error: {msg}"
