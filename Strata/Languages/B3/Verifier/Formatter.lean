/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SMT

/-!
# SMT Term Formatting

Formats SMT terms directly to SMT-LIB syntax without A-normal form.
-/

namespace Strata.B3.Verifier

open Strata.SMT

/-- Format SMT term directly to SMT-LIB syntax -/
partial def formatTermDirect : Term → String
  | Term.prim (.bool b) => if b then "true" else "false"
  | Term.prim (.int i) => toString i
  | Term.prim (.string s) => s!"\"{s}\""
  | Term.var v => v.id
  | Term.quant qk args trigger body =>
      let qkStr := match qk with | .all => "forall" | .exist => "exists"
      let varDecls := args.map (fun v => s!"({v.id} {formatType v.ty})")
      let varDeclsStr := String.intercalate " " varDecls
      match trigger with
      | Term.app .triggers triggerExprs .trigger =>
          if triggerExprs.isEmpty then
            s!"({qkStr} ({varDeclsStr}) {formatTermDirect body})"
          else
            let patternStrs := triggerExprs.map (fun t => s!"({formatTermDirect t})")
            let patternStr := String.intercalate " " (patternStrs.map (fun p => s!":pattern {p}"))
            s!"({qkStr} ({varDeclsStr}) (! {formatTermDirect body} {patternStr}))"
      | _ => s!"({qkStr} ({varDeclsStr}) {formatTermDirect body})"
  | Term.app op args _ =>
      match op with
      | .uf f =>
          let argStrs := args.map formatTermDirect
          if argStrs.isEmpty then
            s!"({f.id})"
          else
            s!"({f.id} {String.intercalate " " argStrs})"
      | .ite => s!"(ite {formatTermDirect args[0]!} {formatTermDirect args[1]!} {formatTermDirect args[2]!})"
      | .eq => s!"(= {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .add => s!"(+ {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .sub => s!"(- {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .mul => s!"(* {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .div => s!"(div {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .mod => s!"(mod {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .lt => s!"(< {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .le => s!"(<= {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .gt => s!"(> {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .ge => s!"(>= {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .not => s!"(not {formatTermDirect args[0]!})"
      | .and => s!"(and {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .or => s!"(or {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .implies => s!"(=> {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .neg => s!"(- {formatTermDirect args[0]!})"
      | _ => s!"(unsupported-op {args.length})"
  | _ => "(unsupported-term)"
where
  formatType : TermType → String
    | .bool => "Bool"
    | .int => "Int"
    | .real => "Real"
    | .string => "String"
    | .bitvec n => s!"(_ BitVec {n})"
    | _ => "UnknownType"

end Strata.B3.Verifier
