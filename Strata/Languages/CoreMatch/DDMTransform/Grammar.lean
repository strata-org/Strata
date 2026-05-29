/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DDMTransform.Grammar
meta import Strata.DDM.Integration.Lean

namespace Strata

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

#dialect
dialect CoreMatch;

import Core;

category MatchPatVar;
@[declare(v, tp)]
op matchPatVar_typed (v : Ident, tp : Type) : MatchPatVar => v " : " tp;

category MatchPatVars;
op matchPatVars_nil  () : MatchPatVars => ;
@[scope(v)]
op matchPatVars_one  (v : MatchPatVar) : MatchPatVars => v;
@[scope(v)]
op matchPatVars_cons (vs : MatchPatVars, @[scope(vs)] v : MatchPatVar) : MatchPatVars =>
  vs ", " v;

category MatchPat;
@[scope(vs)]
op matchPat_ctor (ctor : Ident, vs : MatchPatVars) : MatchPat =>
  ctor "(" vs ")";
op matchPat_wild () : MatchPat => "_";

category MatchStmtArm;
op matchStmtArm_mk (p : MatchPat, @[scope(p)] body : Block) : MatchStmtArm =>
  p " => " body:0;

category MatchStmtArms;
op matchStmtArms_nil  () : MatchStmtArms => ;
op matchStmtArms_cons (arm : MatchStmtArm, arms : MatchStmtArms) : MatchStmtArms =>
  arm "\n  " arms:0;

op match_statement (dt : Type, scrutinee : dt, arms : MatchStmtArms) : Statement =>
  "match " scrutinee " {\n  " arms "\n}";

// Expression-level match. The head arm is surfaced separately so its
// body type pins the result type `tp`; tail arms then carry untyped
// `Expr` bodies. The `arm` keyword anchors tail arms against
// ambiguity with Core operators.
category MatchExprTailArm;
category MatchExprTailArmList;

op matchExprTailArm_mk (p : MatchPat, @[scope(p)] body : Expr) : MatchExprTailArm =>
  "arm " p " => " body:0 ";";

op matchExprTailArmList_nil  () : MatchExprTailArmList => ;
op matchExprTailArmList_cons (a : MatchExprTailArm, as : MatchExprTailArmList) :
  MatchExprTailArmList =>
  a "\n  " as:0;

// Shares the `match` keyword with `match_statement`; the parser
// dispatches by syntactic category (Statement vs Expr).
fn match_expr (dt : Type, tp : Type, scrut : dt,
               headPat : MatchPat, @[scope(headPat)] headBody : tp,
               tailArms : MatchExprTailArmList) : tp =>
  "match " scrut " {" "arm " headPat " => " headBody ";" tailArms "}";

category Program;
op prog (commands : SpacePrefixSepBy Command) : Program =>
  commands;

#end

end Strata

