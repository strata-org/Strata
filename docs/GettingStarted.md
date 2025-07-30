## Creating a New Strata Dialect + Analysis using Existing Dialects

Strata provides composable building blocks that aim to reduce the
overhead of developing new intermediate representations and
analyses. In this [example](../StrataTest/DL/Imperative), we show
some of Strata's current capabilities by defining a simple Strata
dialect called `ArithPrograms` and an associated deductive verifier
based on the existing [Imperative](../Strata/DL/Imperative)
dialect in Strata's Dialect Library ([DL](../Strata/DL)). 
`Imperative` provides basic commands and statements, is 
parameterizable by expressions, and has a parameterizable partial 
evaluator that generates verification conditions.

### 1. Design the concrete syntax

Strata's [Dialect Definition Mechanism (DDM)](../Strata/DDM)
offers the ability to define a dialect's concrete syntax in a
declarative fashion, after which we get parsing, preliminary type
checking, and (de)serialization capabilities. The DDM definition for
`ArithPrograms` is
[here](../StrataTest/DL/Imperative/DDMDefinition.lean).

E.g., an expression definition in `ArithPrograms` looks like the following:
```bash
fn add_expr (a : num, b : num) : num => @[prec(25), leftassoc] a "+" b;
```
and a command declaration for an assertion is as follows, where
`c` is an expression of type `bool`.
```bash
op assert (label : Label, c : bool) : Command => "assert " label c ";\n";
```

We can now write programs in DDM's environment using our concrete
syntax, as follows:
```bash
private def testEnv :=
#strata
open ArithPrograms;
init x : num := 0;
assert [test]: (x == 0);
#end
```

The DDM also offers a capability to generate Lean types automatically
from these definitions using the following command:
```bash
#strataGenAST ArithPrograms
```

For instance, we can see the generated type for expressions in
`ArithPrograms` as follows:
```bash
/--
inductive ArithPrograms.Expr : Type
number of parameters: 0
constructors:
ArithPrograms.Expr.fvar : Nat → Expr
ArithPrograms.Expr.numLit : Nat → Expr
ArithPrograms.Expr.btrue : Expr
ArithPrograms.Expr.bfalse : Expr
ArithPrograms.Expr.add_expr : Expr → Expr → Expr
ArithPrograms.Expr.mul_expr : Expr → Expr → Expr
ArithPrograms.Expr.eq_expr : ArithProgramsType → Expr → Expr → Expr
-/
#guard_msgs in
#print Expr
```

### 2. Design the abstract syntax and implement a concrete-to-abstract syntax translator

A good design choice for abstract syntax is one that is amenable to
transformations, debugging, and analyses. The DDM-generated code may
or may not serve your purpose. For example, for `ArithPrograms`,
perhaps you would like to see named variables instead of de Bruijn
indices (see `.fvar` above).

The abstract syntax for expressions in `ArithPrograms` is defined
[here](../StrataTest/DL/Imperative/ArithExpr.lean). For our simple
dialect, this is in fact quite similar to the DDM-generated one,
except that we have `Var : String → Option Ty` that have both the
variable names and optionally their types instead of DDM's `.fvar`s.

```bash
inductive Arith.Expr where
  | Plus (e1 e2 : Expr)
  | Mul (e1 e2 : Expr)
  | Eq (e1 e2 : Expr)
  | Num (n : Nat)
  | Bool (b : Bool)
  | Var (v : String) (ty : Option Ty)
```

We can obtain the abstract syntax for commands in `ArithPrograms` by
parameterizing `Imperative`'s commands, like so:
```bash
abbrev Arith.Commands := Imperative.Cmds Arith.PureExpr
```

Translation from the DDM-generated types to this abstract syntax is
done [here](../StrataTest/DL/Imperative/DDMTranslate.lean).

### 3. Instantiate `Imperative`'s type checker and partial evaluator

`Imperative` comes with an implementation of a [type
checker](../Strata/DL/Imperative/CmdType.lean) and a [partial
evaluator](../Strata/DL/Imperative/CmdEval.lean), parameterized by
the [`TypeContext`](../Strata/DL/Imperative/TypeContext.lean) and
[`EvalContext`](../Strata/DL/Imperative/EvalContext.lean)
typeclasses respectively. Instantiations of these typeclasses with
appropriate functions will give us implementations for
`ArithPrograms`.

E.g., the following `ArithPrograms`' function is used to instantiate
the type unifier in the `TypeContext` class. There is no polymorphism
in `ArithPrograms`, so two types unify only if they are exactly equal.
```bash
def unifyTypes (T : TEnv) (constraints : List (Ty × Ty)) : Except Format TEnv :=
  match constraints with
  | [] => .ok T
  | (t1, t2) :: crest =>
    if t1 == t2 then
      unifyTypes T crest
    else
      .error f!"Types {t1} and {t2} cannot be unified!"
```

Analogously, the partial evaluator for expressions in the `EvalContext` class is
instantiated by the following straightforward function:
```bash
def eval (s : State) (e : Expr) : Expr :=
  match e with
  | .Plus e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .Num n1, .Num n2 => .Num (n1 + n2)
    | e1', e2' => .Plus e1' e2'
  | .Mul e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .Num n1, .Num n2 => .Num (n1 * n2)
    | e1', e2' => .Mul e1' e2'
  | .Eq e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .Num n1, .Num n2 =>
      (if n1 == n2 then .Bool true else .Bool false)
    | e1', e2' => .Eq e1' e2'
  | .Num n => .Num n
  | .Bool b => .Bool b
  | .Var v ty => match s.env.find? v with | none => .Var v ty | some (_, e) => e
```

At this point, we can type-check `ArithPrograms` and generate
verification conditions for well-typed `ArithPrograms`. Here's an
example of a small program that is verified by the partial evaluator
itself:
```bash
private def testProgram1 : Commands :=
  [.init "x" .Num (.Num 0),
   .set "x" (.Plus (.Var "x" .none) (.Num 100)),
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Num 100))]

/--
info:
Obligation x_value_eq proved via evaluation!

---
info: ok: Commands:
init (x : Num) := 0
x := 100
assert [x_value_eq] true

State:
error: none
deferred: #[]
pathConditions: ⏎
env: (x, (Num, 100))
genNum: 0
-/
#guard_msgs in
#eval do let (cmds, S) ← typeCheckAndPartialEval testProgram1
         return format (cmds, S)
```

Here's an example of a small program for which the VC `x_value_eq` is
generated (that will not pass verification once we plug in a reasoning
backend). All such VCs are deferred -- they are stored in the
evaluation environment so that they can be discharged later; see
`deferObligation` in the
[`EvalContext`](../Strata/DL/Imperative/EvalContext.lean) class.

```bash
private def testProgram2 : Commands :=
  [.init "x" .Num (.Var "y" (.some .Num)),
   .havoc "x",
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Var "y" none))]

/--
info: ok: Commands:
init (x : Num) := (y : Num)
#[<var x: ($__x0 : Num)>] havoc x
assert [x_value_eq] ($__x0 : Num) = (y : Num)

State:
error: none
deferred: #[Label: x_value_eq
 Assumptions:
 Obligation: ($__x0 : Num) = (y : Num)
 Metadata:
 ]
pathConditions:
env: (y, (Num, (y : Num))) (x, (Num, ($__x0 : Num)))
genNum: 1
-/
#guard_msgs in
#eval do let (cmds, S) ← typeCheckAndPartialEval testProgram2
         return format (cmds, S)
```

### 4. Write an encoder from `ArithPrograms`' expressions to SMTLIB

The generated VCs are in terms of `ArithPrograms`' expressions. Given
their simplicity, it is fairly straightforward to encode them to
SMTLIB using Strata's [SMT dialect](../Strata/DL/SMT). Strata's SMT
dialect provides support for some core theories, like uninterpreted
functions with equality, integers, quantifiers, etc., and some basic
utilities, like a counterexample parser and file I/O function to write
SMTLIB files.

The SMT encoding for `ArithPrograms` is done
[here](../StrataTest/DL/Imperative/SMTEncoder.lean). E.g., here is
the core encoding function:
```bash
def toSMTTerm (E : Env) (e : Arith.Expr) : Except Format Term := do
  match e with
  | .Plus e1 e2 =>
    let e1 ← toSMTTerm E e1
    let e2 ← toSMTTerm E e2
    .ok (Term.app Op.add [e1, e2] .int)
  | .Mul e1 e2 =>
    let e1 ← toSMTTerm E e1
    let e2 ← toSMTTerm E e2
    .ok (Term.app Op.mul [e1, e2] .int)
  | .Eq e1 e2 =>
    let e1 ← toSMTTerm E e1
    let e2 ← toSMTTerm E e2
    .ok (Term.app Op.eq [e1, e2] .bool)
  | .Num n => .ok (Term.int n)
  | .Bool b => .ok (Term.bool b)
  | .Var v ty =>
    match ty with
    | none => .error f!"Variable {v} not type annotated; SMT encoding failed!"
    | some ty =>
      let ty ← toSMTType ty
      .ok (TermVar.mk false v ty)
```

### 5. Write basic plumbing utilities to start verifying `ArithPrograms`

We now have all the pieces in place to build an end-to-end verifier
for `ArithPrograms`. We hook up the DDM translator with the type
checker + partial evaluator, followed by the SMT encoder. We then
write some basic functions to invoke an SMT solver on every deferred
VC [here](../StrataTest/DL/Imperative/Verify.lean).

Some example programs can be found
[here](../StrataTest/DL/Imperative/Examples.lean).

```bash
def testProgram : Environment :=
#strata
open ArithPrograms;
  var x : num;
  assert [double_x_lemma]: (2 * x == x + x);
#end

/--
info: Wrote problem to vcs/double_x_lemma.smt2.
---
info:
Obligation: double_x_lemma
Result: verified
-/
#guard_msgs in
#eval Strata.ArithPrograms.verify "cvc5" testProgram
```

To invoke the verifier from the command-line, you can also add support
for `ArithPrograms` in [`StrataVerify`](../StrataVerify.lean).

## Next Steps

Now that you have set up Strata and created a basic dialect, here are
some next steps to explore:

- **Study Existing Dialects**: Look at the implementation of the
  `Imperative` and `Lambda` dialects, and understand how they are used
  as building blocks for the existing `Boogie` and `C_Simp` dialects.

- **Add a New Dialect**: Create a new dialect that captures a language
  construct that you want to formalize and reason about. Perhaps you
  want to *transform* your new dialect into an existing Strata dialect
  to leverage any analysis available for the latter. You may also want
  to verify any such dialect transformations, i.e., prove that they
  are semantics-preserving. One such example in Strata is for call 
  eliminiation in Boogie, [here](../Strata/Transform/).

- **Create a Language Frontend**: Develop a parser to translate the
  concrete syntax of your language of interest to Strata.

- **Add an Analysis Backend**: Add analyses backends for Strata
  programs (e.g., denotations into the logic of Lean or another
  prover, model checkers, static analyzers, etc.).

- **Contribute to Strata**: Consider contributing your dialect or
  improvements back to the Strata project.
