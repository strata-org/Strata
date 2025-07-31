/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.NondetStmt
import Strata.Languages.Boogie.StatementType

open Imperative
mutual

def StmtToNondetStmt {P : PureExpr} [Imperative.HasBool P] [Imperative.HasBoolNeg P]
  (st : Imperative.Stmt P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match st with
  | .cmd    cmd => .cmd cmd
  | .block  _ b _ => StmtsToNondetStmt b.ss
  | .ite    cond  thenb elseb md =>
    .choice
      (.seq (.assert "true_cond" cond md) (StmtsToNondetStmt thenb.ss))
      (.seq ((.assert "false_cond" (Imperative.HasBoolNeg.neg cond) md)) (StmtsToNondetStmt elseb.ss))
  | .loop   guard _measure _inv body md =>
    .loop (.seq (.assume "guard" guard md) (StmtsToNondetStmt body.ss))
  -- TODO: need goto equivalent
  | .goto _ _ => (.assert "skip" Imperative.HasBool.tt)
  termination_by (sizeOf st)
  decreasing_by all_goals simp [sizeOf] <;> omega

def StmtsToNondetStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [Imperative.HasBoolNeg P]
  (ss : Imperative.Stmts P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match ss with
  | [] => (.assert "skip" Imperative.HasBool.tt)
  | s :: ss => .seq (StmtToNondetStmt s) (StmtsToNondetStmt ss)
  termination_by (sizeOf ss)
  decreasing_by all_goals simp [sizeOf]; omega
end
