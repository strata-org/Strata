/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SMT

/-!
# SMT Term Formatting

Formats SMT terms directly to SMT-LIB syntax without A-normal form.

## Why not use Encoder.termToString?

The SMT Encoder (`Strata.DL.SMT.Encoder`) is designed for full verification pipelines
and produces A-normal form (ANF) output with intermediate definitions:

```smt2
(define-fun t0 () Int (+ 1 1))
(define-fun t1 () Bool (= t0 2))
(assert t1)
```

For B3 verification, we want direct, readable SMT-LIB that matches B3's output:

```smt2
(assert (= (+ 1 1) 2))
```

This formatter provides direct translation without ANF, making the output:
- More readable for debugging
- Matches B3's SMT generation
- Simpler for our use case (no need for state management)

If we need ANF in the future (e.g., for term sharing), we can switch to using the Encoder.
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
