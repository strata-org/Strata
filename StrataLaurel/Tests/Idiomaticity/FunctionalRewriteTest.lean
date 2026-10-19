/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the `FunctionalRewrite` pass turns an imperative transparent body
into a single pure expression by continuation passing, and reports the bodies
that have no functional form.

The pass runs on the `$asFunction` copies made by the transparency pass, after
`EliminateReturnStatements` has lowered every `return e` into
`output := e; exit $return`. So the input programs below are written with
`return`, and the driver runs `eliminateReturnStatements` as the input-shaping
predecessor, so what the pass receives is in `exit $return` form.

Each golden is the body after the pass. Three rules show in them: an `exit $return`
becomes a reference to the output parameter, an assignment becomes a
*declaration* scoping over the statements that follow it, and the statements
after an if become the continuation of *both* branches.

The snippets use no operators: a branch condition is a `bool` parameter, and
where a value has to be a function of the previous one the snippet declares its
own opaque `step` rather than writing `+ 1`. That is because every operator is a
call to a prelude wrapper, and the pass cannot be run with the prelude attached —
see `printRewritten`.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.EliminateReturnStatements

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Parse, resolve, run `functionalRewritePass`, print the rewritten function
    bodies. `functionalRewritePass` takes functions whose `return`s have already
    been eliminated, so `eliminateReturnStatements` runs as the input-shaping
    predecessor and the procedures are placed in the `functions` bucket (the pass
    rewrites function copies; `coreProcedures` are left alone).

    `prelude := false`: a prelude operator wrapper such as `$add` is itself a
    bodied function, so with the prelude attached the pass binds each one's output
    to a generated hole — forty-odd of them. Filtering those out by name would be
    easy enough (they are `$declHole_$add_…` and friends); what makes the prelude
    unusable here is that the trailing id is a GLOBAL resolver counter, so those
    holes claim the low numbers and every golden below renumbers — `$declHole_guard_3`
    becomes `$declHole_guard_562`, and shifts again whenever the prelude changes.
    The snippets therefore avoid operators entirely so they resolve without it. -/
private def printRewritten (program : StrataDDM.Program) : IO Unit :=
  runCorePassForIdiomaticity functionalRewritePass
    (fun p _ => { functions := (eliminateReturnStatements p).staticProcedures,
                  coreProcedures := [], datatypes := [], constants := [] })
    program (prelude := false)

/-! ## A guard early exit becomes an if-expression

The statements after the `if` are the continuation of both branches. The
exiting branch discards it and yields the output, so it keeps only `r := 1`;
the fall-through branch carries the rest of the body. The `if` does not need to
be the last statement of its block. -/

/--
info: procedure $declHole_guard_3(b: bool): int
  opaque;
procedure guard(b: bool)
  returns (r: int)
{
  var r: int := $declHole_guard_3(b);
  if b
    then {
      var r: int := 1;
      r
    }
    else {
      var r: int := 3;
      r
    }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure guard(b: bool) returns (r: int) {
  if b then {
    return 1
  };
  return 3
};
#end

/-! ## Chained guards nest, and duplicate the continuation

Each guard's continuation is everything after it, so the second guard and the
final return are substituted into the first guard's `else`. With n chained
fall-through ifs this is 2^n copies of the trailing code — the known cost of
having no `let` in Core to bind the continuation once. -/

/--
info: procedure $declHole_chainedGuards_4(b: bool, c: bool): int
  opaque;
procedure chainedGuards(b: bool, c: bool)
  returns (r: int)
{
  var r: int := $declHole_chainedGuards_4(b, c);
  if b
    then {
      var r: int := 1;
      r
    }
    else if c
      then {
        var r: int := 2;
        r
      }
      else {
        var r: int := 3;
        r
      }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure chainedGuards(b: bool, c: bool) returns (r: int) {
  if b then {
    return 1
  };
  if c then {
    return 2
  };
  return 3
};
#end

/-! ## Code after an if whose branches both exit is dropped

Both branches end in `exit $return`, so neither uses the continuation, and the
trailing `return 3` disappears rather than being duplicated. It is unreachable,
so dropping it is what the imperative body means. -/

/--
info: procedure $declHole_deadCodeAfterIfElse_3(b: bool): int
  opaque;
procedure deadCodeAfterIfElse(b: bool)
  returns (r: int)
{
  var r: int := $declHole_deadCodeAfterIfElse_3(b);
  if b
    then {
      var r: int := 1;
      r
    }
    else {
      var r: int := 2;
      r
    }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure deadCodeAfterIfElse(b: bool) returns (r: int) {
  if b then {
    return 1
  } else {
    return 2
  };
  return 3
};
#end

/-! ## Nested ifs where every path exits

The inner if is in tail position of the outer `then`, so nothing follows it and
its continuation is unused. Every path exits, so the result is a plain nest of
if-expressions with no duplication. -/

/--
info: procedure $declHole_nestedIf_4(b: bool, c: bool): int
  opaque;
procedure nestedIf(b: bool, c: bool)
  returns (r: int)
{
  var r: int := $declHole_nestedIf_4(b, c);
  if b
    then if c
      then {
        var r: int := 1;
        r
      }
      else {
        var r: int := 2;
        r
      }
    else {
      var r: int := 3;
      r
    }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure nestedIf(b: bool, c: bool) returns (r: int) {
  if b then {
    if c then {
      return 1
    } else {
      return 2
    }
  } else {
    return 3
  }
};
#end

/-! ## A nested guard duplicates the continuation along every falling path

Here the inner if has no `else` and the outer if has no `else`, so `return 2` is
the continuation of three separate paths: inner-false, and outer-false. It
therefore appears three times in the result. This is the 2^n growth compounding
through nesting, and the clearest illustration of why binding the continuation
once matters. -/

/--
info: procedure $declHole_nestedGuard_4(b: bool, c: bool): int
  opaque;
procedure nestedGuard(b: bool, c: bool)
  returns (r: int)
{
  var r: int := $declHole_nestedGuard_4(b, c);
  if b
    then if c
      then {
        var r: int := 1;
        r
      }
      else {
        var r: int := 2;
        r
      }
    else {
      var r: int := 2;
      r
    }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure nestedGuard(b: bool, c: bool) returns (r: int) {
  if b then {
    if c then {
      return 1
    }
  };
  return 2
};
#end

/-! ## A destructive update becomes a shadowing declaration

`x := step(x)` turns into a second `var x` nested inside the scope of the first.
Shadowing is legal because `Resolution.defineNameCheckDup` is per-scope and the
declaration goes in a fresh block, and the update still reads the previous
binding because the initializer resolves in the *enclosing* scope — which is what
the nested `var $v_4: int := step($v_4)` below shows.
`InlineLocalVariables` then inlines both declarations away. -/

/--
info: procedure $declHole_updateLocal_6(a: int): int
  opaque;
procedure step(n: int)
  returns (m: int)
  opaque;
procedure updateLocal(a: int)
  returns (r: int)
{
  var r: int := $declHole_updateLocal_6(a);
  {
    var $v_7: int := a;
    {
      var $v_7: int := step($v_7);
      {
        var r: int := $v_7;
        r
      }
    }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure step(n: int) returns (m: int) opaque;
procedure updateLocal(a: int) returns (r: int) {
  var x: int := a;
  x := step(x);
  return x
};
#end

/-! ## An if that assigns a local in both branches needs no if-lifting

Each branch becomes `{ var x := ...; <continuation> }`, so the assignment and
the code that reads it end up in the same branch. Inlining collapses them
afterwards. There is no restriction on how many variables a branch assigns. -/

/--
info: procedure $declHole_ifAssignsLocal_4(b: bool, a: int): int
  opaque;
procedure ifAssignsLocal(b: bool, a: int)
  returns (r: int)
{
  var r: int := $declHole_ifAssignsLocal_4(b, a);
  {
    var $v_5: int := 0;
    if b
      then {
        var $v_5: int := a;
        {
          var r: int := $v_5;
          r
        }
      }
      else {
        var $v_5: int := 1;
        {
          var r: int := $v_5;
          r
        }
      }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure ifAssignsLocal(b: bool, a: int) returns (r: int) {
  var x: int := 0;
  if b then {
    x := a
  } else {
    x := 1
  };
  return x
};
#end

/-! ## An exit to a user label becomes that block's continuation

A labelled block binds its label to the translation of whatever follows it, so
`exit L` evaluates to that — the same rule as `exit $return`, which evaluates to
the output. Here the exiting path skips `y := 2` and the fall-through path runs
it, and both then continue into `return y`. -/

/--
info: procedure $declHole_exitSkipsRest_3(b: bool): int
  opaque;
procedure exitSkipsRest(b: bool)
  returns (r: int)
{
  var r: int := $declHole_exitSkipsRest_3(b);
  {
    var $v_4: int := 0;
    if b
      then {
        var $v_4: int := 1;
        {
          var r: int := $v_4;
          r
        }
      }
      else {
        var $v_4: int := 2;
        {
          var r: int := $v_4;
          r
        }
      }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure exitSkipsRest(b: bool) returns (r: int) {
  var y: int := 0;
  {
    if b then {
      y := 1;
      exit done
    };
    y := 2
  } done;
  return y
};
#end

/-! ## A labelled block ending the body

When the labelled block is the last statement, its continuation is the body's own
continuation — a read of the output. So `exit done` here yields `r` while it is still
unassigned, and because the output is bound to a hole at the top of the body like any
other uninitialized variable, that read is the hole rather than a free reference. This
is the imperative reading of running off the end without assigning the output. -/

/--
info: procedure $declHole_exitToLabel_3(b: bool): int
  opaque;
procedure exitToLabel(b: bool)
  returns (r: int)
{
  var r: int := $declHole_exitToLabel_3(b);
  if b
    then r
    else {
      var r: int := 1;
      r
    }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure exitToLabel(b: bool) returns (r: int) {
  {
    if b then {
      exit done
    };
    return 1
  } done
};
#end

/-! ## A labelled block with statements after it

The block's statements are translated with the label bound to the continuation of
the *block*, so the trailing statements are reached both by exiting and by falling
off the end. -/

/--
info: procedure $declHole_labelledBlockNotLast_3(x: int): int
  opaque;
procedure labelledBlockNotLast(x: int)
  returns (r: int)
{
  var r: int := $declHole_labelledBlockNotLast_3(x);
  {
    var r: int := 1;
    {
      var r: int := 2;
      r
    }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure labelledBlockNotLast(x: int) returns (r: int) {
  {
    r := 1
  } done;
  return 2
};
#end

/-! ## A block-valued assignment functionalizes the block's statements

An assignment's value is normally an expression, but the transparency pass can emit
a transparent body as `$result := { <statements>; <tail expression> }`, whose
statements are genuinely in statement position. Those are functionalized with the
block's own last element as the continuation — so the destructive update inside the
block below becomes a nested shadowing declaration, exactly as it would at
statement level. This is the only shape where a *value* is descended into. -/

/--
info: procedure $declHole_blockValued_6(a: int): int
  opaque;
procedure step(n: int)
  returns (m: int)
  opaque;
procedure blockValued(a: int)
  returns (r: int)
{
  var r: int := $declHole_blockValued_6(a);
  {
    var r: int := {
      var $v_7: int := a;
      {
        var $v_7: int := step($v_7);
        $v_7
      }
    };
    {
      var r: int := r;
      r
    }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure step(n: int) returns (m: int) opaque;
procedure blockValued(a: int) returns (r: int) {
  r := { var y: int := a; y := step(y); y };
  return r
};
#end

/-! ## A declaration with no initializer is bound to a hole

`var x : int;` has no value to bind, and an uninitialized local reads as an
arbitrary value, so it is bound to a deterministic hole: a call to the generated
uninterpreted function `$declHole_<uniqueId>`. The hole takes the enclosing
function's inputs, so its value may depend on them.

The call is *hoisted* to the top of the body and bound to `$declHoleVal_<uniqueId>`,
which the declaration then refers to. Hoisting is what keeps the arguments meaning
the inputs: left where the declaration sits, a body that shadows an input with a
local of the same name would capture the argument, the hole would stop varying with
that input, and a caller could prove `f(1) == f(2)`.

The later `x := a` becomes a *shadowing* declaration nested inside, exactly as
any other assignment does, so the hole is only what `x` holds before that
assignment — here, nothing reads it. Binding unconditionally rather than dropping
the declaration is what makes the rewrite sound: a dropped declaration leaves a
free reference on any path that never assigns, and if the name shadows an input
parameter that reference silently resolves to the input. -/

/--
info: procedure $declHole_uninitThenAssign_3(a: int): int
  opaque;
procedure $declHole_uninitThenAssign_4(a: int): int
  opaque;
procedure uninitThenAssign(a: int)
  returns (r: int)
{
  var r: int := $declHole_uninitThenAssign_3(a);
  {
    var $declHoleVal_4: int := $declHole_uninitThenAssign_4(a);
    {
      var $v_4: int := $declHoleVal_4;
      {
        var $v_4: int := a;
        {
          var r: int := $v_4;
          r
        }
      }
    }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure uninitThenAssign(a: int) returns (r: int) {
  var x: int;
  x := a;
  return x
};
#end

/-! ### A local that is never assigned at all

Nothing shadows the hole here, so the body evaluates to it directly: the function
returns an arbitrary-but-fixed value. It is *fixed* rather than arbitrary-per-call
because the hole is an uninterpreted function, which is what lets a transparent body
stay a function; with no inputs to depend on, this one is nullary. -/

/--
info: procedure $declHole_uninitRead_2(): int
  opaque;
procedure $declHole_uninitRead_3(): int
  opaque;
procedure uninitRead()
  returns (r: int)
{
  var r: int := $declHole_uninitRead_2();
  {
    var $declHoleVal_3: int := $declHole_uninitRead_3();
    {
      var $v_3: int := $declHoleVal_3;
      {
        var r: int := $v_3;
        r
      }
    }
  }
};
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure uninitRead() returns (r: int) {
  var x: int;
  return x
};
#end

/-! ## A body with no outputs is left alone, without a diagnostic

There is nothing for a function copy of a void procedure to evaluate to, so the
copy is left untransformed rather than reported; the procedure itself carries
the meaning. This has to stay legal — `valuelessEarlyReturn` is a transparent
body with no outputs that must verify. -/

/--
info: procedure valueless(b: bool)
{
  if b
    then {
      exit $return
    };
  exit $return
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure valueless(b: bool) {
  if b then {
    return
  };
  return
};
#end

/-! ## Bodies with no functional form are reported, and left untouched

In each case below the body comes back in its pre-pass `exit $return` form:
the rewrite is all-or-nothing, so a rejected body is returned unchanged
alongside its diagnostic. Because acceptance and transformation are the same
recursive function, a construct cannot be admitted by a guard that the rewrite
then mishandles.

The diagnostics come in two kinds. A construct the user can legitimately write
in a transparent body is a `userError` — the body simply is not expressible as a
function. A construct an earlier pass is supposed to have eliminated is a
`strataBug`: reaching one means the pipeline is misordered, so the message names
the pass responsible rather than blaming the user. The cases below drive the pass
directly, which is how the `strataBug` paths are reachable at all; in the real
pipeline the transparency pass strips asserts and assumes from the function copy
and rewrites calls into functional form, so those bodies arrive here clean. -/

/-! ### A loop -/

/--
info: FunctionalRewritePass diagnostic[userError]: loops are not YET supported in transparent bodies or contracts
procedure step(n: int)
  returns (m: int)
  opaque;
procedure hasLoop(b: bool)
  returns (r: int)
{
  var i: int := 0;
  while(b) {
    i := step(i)
  };
  {
    r := i;
    exit $return
  }
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure step(n: int) returns (m: int) opaque;
procedure hasLoop(b: bool) returns (r: int) {
  var i: int := 0;
  while (b) {
    i := step(i)
  };
  return i
};
#end

/-! ### An assert -/

/--
info: FunctionalRewritePass diagnostic[error]: assert should have been stripped from the function copy by the transparency pass
procedure hasAssert(b: bool)
  returns (r: int)
{
  assert b;
  {
    r := 1;
    exit $return
  }
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure hasAssert(b: bool) returns (r: int) {
  assert b;
  return 1
};
#end

/-! ### An assume -/

/--
info: FunctionalRewritePass diagnostic[error]: assume should have been stripped from the function copy by the transparency pass
procedure hasAssume(b: bool)
  returns (r: int)
{
  assume b;
  {
    r := 1;
    exit $return
  }
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure hasAssume(b: bool) returns (r: int) {
  assume b;
  return 1
};
#end

/-! ### An assignment to an input parameter

This is a destructive assignment the Core translator must keep rejecting.
Turning it into a shadowing declaration would silently accept the program, so
input names are checked before the binding rule applies. -/

/--
info: FunctionalRewritePass diagnostic[userError]: a transparent body or contract cannot YET mutate any of its inputs, and this mutates 'a'
procedure step(n: int)
  returns (m: int)
  opaque;
procedure assignsInput(a: int)
  returns (r: int)
{
  a := step(a);
  {
    r := a;
    exit $return
  }
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure step(n: int) returns (m: int) opaque;
procedure assignsInput(a: int) returns (r: int) {
  a := step(a);
  return a
};
#end

/-! ### More than one output

A function evaluates to a single value, so there is no way for one to yield
several outputs at once. This needs a tuple construct in Laurel, or a real
`let` in Core. -/

/--
info: FunctionalRewritePass diagnostic[userError]: a transparent body with 2 output parameters is not supported; it must have at most one
procedure twoOuts()
  returns (q: int, r: int)
{
  q := 1;
  r := 2
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure twoOuts() returns (q: int, r: int) {
  q := 1;
  r := 2
};
#end

/-! ### A call in statement position

Only the calling body is reported; `callee` is rewritten as usual, showing that
one rejected body does not stop the others. -/

/--
info: FunctionalRewritePass diagnostic[error]: call should have been rewritten to functional form by the transparency pass
procedure $declHole_callee_3(): int
  opaque;
procedure callee()
  returns (r: int)
{
  var r: int := $declHole_callee_3();
  {
    var r: int := 1;
    r
  }
};
procedure hasCall()
  returns (r: int)
{
  var y: int := 0;
  callee();
  {
    r := y;
    exit $return
  }
}$return;
-/
#guard_msgs in
#eval printRewritten <|
#strata
program Laurel;
procedure callee() returns (r: int) {
  return 1
};
procedure hasCall() returns (r: int) {
  var y: int := 0;
  callee();
  return y
};
#end

end Laurel
