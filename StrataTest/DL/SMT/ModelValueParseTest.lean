/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.SMTUtils
meta import Strata.Languages.Core.SMTEncoder
meta import StrataTest.DL.SMT.ModelTestHarness

meta section

/-! ## How each solver spelling of a `get-value` value is read

A counterexample is only as good as the values read back from the solver. Each row
below is a `(get-value …)` response, most of them printed by z3 4.12 or cvc5 1.3 on
Strata queries, and pins the four stages a value goes through:

* how many valuation pairs `parseModelDDM` returns (`0 pair(s)`: nothing was read);
* the parsed `SMT.Term`, rendered back to SMT-LIB (`termToString`);
* its Core lift (`smtTermToLExpr`);
* whether the lift is a value the VC check may use (`smtTermIsValue`, the `value?` flag).

`Cons`, `Nil` and `mk` are the constructor names in scope.
-/

open Imperative.SMT Strata.SMT.ModelTestHarness

/-- The constructor names the rows are read with. -/
private def ctors : Std.HashSet String := ({} : Std.HashSet String).insert "Cons"
  |>.insert "Nil" |>.insert "mk"

/-- Print what one response yields: the pair count, then one line per pair. -/
private def probe (label : String) (resp : String) : IO Unit := do
  let pairs ← parseModelDDM resp
  IO.println s!"{label}: {pairs.length} pair(s)"
  for (k, t) in pairs do
    let term := (Strata.SMTDDM.termToString t).toOption.getD "<unrenderable>"
    IO.println s!"  {k} | {term} | {Std.format (Core.smtTermToLExpr t ctors)} | \
      {Core.smtTermIsValue t ctors}"

/-! ### Literals -/

/--
info: bool: 2 pair(s)
  x | true | true | true
  y | false | false | true
int: 1 pair(s)
  x | 5 | 5 | true
int-neg: 1 pair(s)
  x | (- 5) | int.neg(5) | true
int-big: 1 pair(s)
  x | 123456789012345678901234567890 | 123456789012345678901234567890 | true
real-dec: 1 pair(s)
  r | 1.5 | 1.5 | true
real-neg: 1 pair(s)
  r | (- 1.5) | real.neg(1.5) | true
real-z3-ratio: 1 pair(s)
  r | (|`2F| 1.0 3.0) | frac{1, 3} | true
real-z3-negratio: 1 pair(s)
  r | (|`2D| (|`2F| 1.0 3.0)) | real.neg(frac{1, 3}) | true
real-cvc5-ratio: 1 pair(s)
  r | (|`2F| 1 3) | frac{1, 3} | true
real-cvc5-negratio: 1 pair(s)
  r | (|`2F| (- 1) 3) | real.neg(frac{1, 3}) | true
real-zero-den: 1 pair(s)
  r | (|`2F| 1 0) | |/|(1, 0) | false
bv-bin: 1 pair(s)
  b | (_ bv5 4) | Bv4.Lit(5)
-- Errors: Unsupported construct in lconstToExpr: unsupported bitvec width: 4
Context: Global scope: | true
bv-hex: 1 pair(s)
  b | (_ bv15 8) | bv{8}(15) | true
bv-indexed: 1 pair(s)
  b | (_ bv5 8) | bv{8}(5) | true
str: 1 pair(s)
  s | "abc" | "abc" | true
str-empty: 1 pair(s)
  s | "" | "" | true
-/
#guard_msgs in
#eval do
  probe "bool" "((x true) (y false))"
  probe "int" "((x 5))"
  probe "int-neg" "((x (- 5)))"
  probe "int-big" "((x 123456789012345678901234567890))"
  probe "real-dec" "((r 1.5))"
  probe "real-neg" "((r (- 1.5)))"
  probe "real-z3-ratio" "((r (/ 1.0 3.0)))"
  probe "real-z3-negratio" "((r (- (/ 1.0 3.0))))"
  probe "real-cvc5-ratio" "((r (/ 1 3)))"
  probe "real-cvc5-negratio" "((r (/ (- 1) 3)))"
  probe "real-zero-den" "((r (/ 1 0)))"
  probe "bv-bin" "((b #b0101))"
  probe "bv-hex" "((b #x0f))"
  probe "bv-indexed" "((b (_ bv5 8)))"
  probe "str" "((s \"abc\"))"
  probe "str-empty" "((s \"\"))"

/-! ### Datatypes, uninterpreted sorts, arrays and functions -/

/--
info: dt-cons: 1 pair(s)
  l | (Cons 1 Nil) | Cons(1, Nil) | true
dt-nil: 1 pair(s)
  l | Nil | Nil | true
dt-as-nil: 1 pair(s)
  l | Nil | Nil | true
dt-record: 1 pair(s)
  p | (mk 1 true) | mk(1, true) | true
usort-z3: 1 pair(s)
  u | T!val!0 | T!val!0 | false
usort-cvc5: 1 pair(s)
  u | |`40T_0| | |@T_0| | false
usort-cvc5-as: 1 pair(s)
  u | |`40T_0| | |@T_0| | false
arr-const: 1 pair(s)
  a | (const 0) | |const|(0) | false
arr-store: 1 pair(s)
  a | (store (const 0) 1 5) | store(|const|(0), 1, 5) | false
arr-as-array: 0 pair(s)
z3-fun: 1 pair(s)
  f | (store (const 10) 2 20) | store(|const|(10), 2, 20) | false
cvc5-fun: 0 pair(s)
fp: 1 pair(s)
  f | (fp (_ bv0 1) (_ bv1024 11) (_ bv0 52)) | fp(bv{1}(0), Bv11.Lit(1024), Bv52.Lit(0))
-- Errors: Unsupported construct in lconstToExpr: unsupported bitvec width: 11
Context: Global scope:
  freeVars: [fp]; Unsupported construct in lconstToExpr: unsupported bitvec width: 52
Context: Global scope:
  freeVars: [fp, Bv11.Lit] | false
fp-zero: 1 pair(s)
  f | |`2B| | |+| | false
seq-unit: 1 pair(s)
  q | (seq.unit 1) | seq.unit(1) | false
seq-empty: 1 pair(s)
  q | seq.empty | seq.empty | false
-/
#guard_msgs in
#eval do
  probe "dt-cons" "((l (Cons 1 Nil)))"
  probe "dt-nil" "((l Nil))"
  probe "dt-as-nil" "((l (as Nil (List Int))))"
  probe "dt-record" "((p (mk 1 true)))"
  probe "usort-z3" "((u T!val!0))"
  probe "usort-cvc5" "((u @T_0))"
  probe "usort-cvc5-as" "((u (as @T_0 T)))"
  probe "arr-const" "((a ((as const (Array Int Int)) 0)))"
  probe "arr-store" "((a (store ((as const (Array Int Int)) 0) 1 5)))"
  probe "arr-as-array" "((a (_ as-array k!0)))"
  probe "z3-fun" "((f (store ((as const (Array Int Int)) 10) 2 20)))"
  probe "cvc5-fun" "((f (lambda ((_arg_1 Int)) (ite (= _arg_1 1) 10 20))))"
  probe "fp" "((f (fp #b0 #b10000000000 #x0000000000000)))"
  probe "fp-zero" "((f (_ +zero 11 53)))"
  probe "seq-unit" "((q (seq.unit 1)))"
  probe "seq-empty" "((q (as seq.empty (Seq Int))))"

/-! ### Binders and annotations

A `let` is substituted into its body before the lift. Its bindings are parallel: in
`let-parallel`, the `a` that `b` reads is the outer `a`, `1`. A unary `-` over a let-bound
literal folds into the negative literal, as `(- 5)` does (`let-neg-int`, `let-neg-real`).
An annotation `(! t …)` reads as `t`; a `:named` attribute does not parse, because the
dialect reads `:name` as a keyword of its `get-info` responses. -/

/--
info: let: 1 pair(s)
  x | 5 | 5 | true
let-nested: 1 pair(s)
  x | (Cons 1 (Cons 1 Nil)) | Cons(1, Cons(1, Nil)) | true
let-shadow: 1 pair(s)
  x | 2 | 2 | true
let-parallel: 1 pair(s)
  x | 1 | 1 | true
let-neg-int: 1 pair(s)
  x | (- 5) | int.neg(5) | true
let-neg-real: 1 pair(s)
  r | (- 1.5) | real.neg(1.5) | true
annot: 1 pair(s)
  x | 5 | 5 | true
annot-named: 0 pair(s)
ite: 1 pair(s)
  x | (ite true 1 2) | ite(true, 1, 2) | false
forall: 0 pair(s)
-/
#guard_msgs in
#eval do
  probe "let" "((x (let ((a!1 5)) a!1)))"
  probe "let-nested" "((x (let ((a 1)) (let ((b (Cons a Nil))) (Cons a b)))))"
  probe "let-shadow" "((x (let ((a 1)) (let ((a 2)) a))))"
  probe "let-parallel" "((x (let ((a 1)) (let ((a 2) (b a)) b))))"
  probe "let-neg-int" "((x (let ((a 5)) (- a))))"
  probe "let-neg-real" "((r (let ((a 1.5)) (- a))))"
  probe "annot" "((x (! 5 :pattern (f))))"
  probe "annot-named" "((x (! 5 :named n)))"
  probe "ite" "((x (ite true 1 2)))"
  probe "forall" "((x (forall ((y Int)) (> y 0))))"

/-! ### Bindings used more than once

Solvers share a repeated subterm through a `let`. In `sharedLets n`, each of `n` nested
bindings uses the previous one twice, so the value is the complete binary tree of `Cons`
of depth `n` with leaves `5`, which `let-shared-2` prints in full. The translation
shares the translation of each binding among its uses, so the 720-byte response
`sharedLets 25`, whose value has 2^25 leaves, reads in time linear in its length.
`let-shared-25` prints the length of the leftmost and of the rightmost path of the
value, and the leaves they end in. -/

/-- `((x (let ((a0 5)) (let ((a1 (Cons a0 a0))) … (let ((an (Cons a(n-1) a(n-1)))) an)))))`. -/
private def sharedLets (n : Nat) : String := Id.run do
  let mut body := s!"a{n}"
  for i in [0:n] do
    body := s!"(let ((a{n - i} (Cons a{n - i - 1} a{n - i - 1}))) {body})"
  return s!"((x (let ((a0 5)) {body})))"

/-- The number of applications on the path of `t` that always takes the first argument
    (`first := true`) or always the last one, and the term the path ends in. -/
private partial def edgePath (first : Bool) : Strata.SMT.Term → Nat × Strata.SMT.Term
  | .app _ (a :: as) _ =>
    let (d, leaf) := edgePath first (if first then a else as.getLastD a)
    (d + 1, leaf)
  | t => (0, t)

/--
info: let-shared-2: 1 pair(s)
  x | (Cons (Cons 5 5) (Cons 5 5)) | Cons(Cons(5, 5), Cons(5, 5)) | true
let-shared-25: 720 bytes, 1 pair(s)
  leftmost path 25 to 5, rightmost path 25 to 5
-/
#guard_msgs in
#eval do
  probe "let-shared-2" (sharedLets 2)
  let resp := sharedLets 25
  let pairs ← parseModelDDM resp
  IO.println s!"let-shared-25: {resp.length} bytes, {pairs.length} pair(s)"
  for (_, t) in pairs do
    let (dl, l) := edgePath true t
    let (dr, r) := edgePath false t
    let render (u : Strata.SMT.Term) := (Strata.SMTDDM.termToString u).toOption.getD "?"
    IO.println s!"  leftmost path {dl} to {render l}, rightmost path {dr} to {render r}"

/-! ### Keys, and responses mixing readable and unreadable pairs

A pair that cannot be read costs only its own binding: a value the term translation
rejects (`lambda`) is dropped from the parsed response, and a response that does not
parse as a whole is parsed pair by pair (`annot-named` does not parse). Pair-by-pair
parsing stops at the verdict of a later check (`followed-by-next-check`), but not at a line
inside a value that reads like a verdict (`verdict-word-in-value`). -/

/--
info: key-at: 1 pair(s)
  x@1 | 5 | 5 | true
key-quoted: 1 pair(s)
  |x y| | 5 | 5 | true
mixed-lambda: 2 pair(s)
  x | 5 | 5 | true
  z | 7 | 7 | true
mixed-unparsable: 2 pair(s)
  x | 5 | 5 | true
  z | 7 | 7 | true
mixed-ratio: 2 pair(s)
  x | 5 | 5 | true
  r | (|`2F| 1.0 3.0) | frac{1, 3} | true
mixed-let: 2 pair(s)
  x | 5 | 5 | true
  y | 5 | 5 | true
z3-block: 5 pair(s)
  s | "ab" | "ab" | true
  a | (store (const 5) 2 7) | store(|const|(5), 2, 7) | false
  b | (const true) | |const|(true) | false
  u | U!val!0 | U!val!0 | false
  n | (- 4) | int.neg(4) | true
followed-by-next-check: 1 pair(s)
  x | 5 | 5 | true
verdict-word-in-value: 3 pair(s)
  x | 5 | 5 | true
  s | "a\u{a}sat\u{a}b" | "a\nsat\nb" | true
  z | 7 | 7 | true
-/
#guard_msgs in
#eval do
  probe "key-at" "((x@1 5))"
  probe "key-quoted" "((|x y| 5))"
  probe "mixed-lambda" "((x 5) (a (lambda ((y Int)) y)) (z 7))"
  probe "mixed-unparsable" "((x 5) (y (! 1 :named n)) (z 7))"
  probe "mixed-ratio" "((x 5) (r (/ 1.0 3.0)))"
  probe "mixed-let" "((x 5) (y (let ((a!1 5)) a!1)))"
  probe "z3-block" "((s \"ab\")\n (a (store ((as const (Array Int Int)) 5) 2 7))\n \
    (b ((as const (Array Int Bool)) true))\n (u U!val!0)\n (n (- 4)))"
  probe "followed-by-next-check" "((x 5) (y (! 1 :named n)))\nunsat\n((x 6))"
  probe "verdict-word-in-value"
    "((x 5)\n (s \"a\nsat\nb\")\n (w\nunknown)\n (z 7))\nunsat\n((x 6))"

/-! ### A solver answer with one unreadable value

`solverResult` reads the model of a validity check that asks for `x`, `y` and `z`. The
value of `y` does not parse; the model keeps `x` and `z`. When none of the variables
has a value, the result carries no model. -/

/-- Print the model `solverResult` reads from the validity-check answer `stdout`. -/
private def printAnswer (stdout : String) : IO Unit := do
  let vars : List Core.Expression.TypedIdent :=
    ["x", "y", "z"].map fun n => (⟨n, ()⟩, .forAll [] .int)
  match ← readAnswer vars stdout with
  | .ok (_, .sat m) => IO.println s!"sat {m.map (·.1.name)}"
  | .ok (_, .unknown (some m)) => IO.println s!"unknown {m.map (·.1.name)}"
  | .ok (_, .unknown none) => IO.println "unknown, no model"
  | _ => IO.println "other"

/--
info: sat [x, z]
unknown [x, z]
unknown, no model
-/
#guard_msgs in
#eval do
  printAnswer "sat\n((x 1) (y (! 2 :named n)) (z 3))\n"
  printAnswer "unknown\n((x 1) (y (! 2 :named n)) (z 3))\n"
  printAnswer "unknown\n(error \"no model\")\n"

/-! ### Two checks in one output

With both checks enabled the output holds the satisfiability verdict and its model, then the
validity verdict and its model. A satisfiability check answered `sat` with no values gets no
model: the validity check's model, later in the output, is not read for it. -/

/-- Print both results `solverResult` reads from a two-check answer `stdout` on `x`. -/
private def printBoth (stdout : String) : IO Unit := do
  let vars : List Core.Expression.TypedIdent := [(⟨"x", ()⟩, .forAll [] .int)]
  let value (e : Strata.SMT.Term) := (Strata.SMTDDM.termToString e).toOption.getD "?"
  let render : Result Core.Expression.Ident → String
    | .sat m => s!"sat {m.map fun (v, e) => s!"{v.name}={value e}"}"
    | .unsat => "unsat"
    | .unknown none => "unknown, no model"
    | .unknown (some m) => s!"unknown {m.map (·.1.name)}"
    | _ => "other"
  match ← solverResult intVar vars { exitCode := 0, stdout, stderr := "" }
      (encoderWith ["x"]) "cvc5" true true with
  | .ok (sr, vr) => IO.println s!"{render sr} / {render vr}"
  | .error _ => IO.println "error"

/--
info: sat [] / sat [x=7]
sat [x=1] / sat [x=7]
-/
#guard_msgs in
#eval do
  printBoth "sat\nsat\n((x 7))\n"
  printBoth "sat\n((x 1))\nsat\n((x 7))\n"

end
