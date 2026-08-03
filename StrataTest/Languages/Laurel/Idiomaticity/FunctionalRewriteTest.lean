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
`return`, and the printer resolves them and runs `eliminateReturnStatements`
before the pass — the `-- before --` output is therefore in `exit $return` form,
which is what the pass actually receives.

Each case prints the body immediately before and immediately after the pass.
Reading the two together shows the three rules that matter: an `exit $return`
becomes a reference to the output parameter, an assignment becomes a
*declaration* scoping over the statements that follow it, and the statements
after an if become the continuation of *both* branches.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.FunctionalRewrite
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Parse + resolve a program, lower its returns, then print every function body
    immediately before and immediately after `functionalRewritePass`, followed by
    any diagnostics the pass reported.

    The procedures go in `functions` rather than `coreProcedures` because the
    pass rewrites function copies; `coreProcedures` are left alone. -/
private def printRewritten (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let lowered := eliminateReturnStatements result.program
  let uc : UnorderedCoreWithLaurelTypes :=
    { functions := lowered.staticProcedures, coreProcedures := [],
      datatypes := [], constants := [] }
  let (uc', diags, _) := functionalRewritePass.run {} uc result.model
  IO.println "-- before --"
  for proc in uc.functions do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))
  IO.println "-- after --"
  for proc in uc'.functions do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))
  for d in diags do
    IO.println s!"diagnostic[{d.kind}]: {d.message}"

/-! ## A guard early exit becomes an if-expression

The statements after the `if` are the continuation of both branches. The
exiting branch discards it and yields the output, so it keeps only `r := 1`;
the fall-through branch carries the rest of the body. The `if` does not need to
be the last statement of its block. -/

/--
info: -- before --
procedure guard(x: int)
  returns (r: int)
{
  if x > 0
    then {
      {
        r := 1;
        exit $return
      }
    };
  {
    r := 3;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(x: int): int
  opaque;
procedure guard(x: int)
  returns (r: int)
{
  var r: int := $declHole_3(x);
  if x > 0
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
#eval printRewritten
#strata
program Laurel;
procedure guard(x: int) returns (r: int) {
  if x > 0 then {
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
info: -- before --
procedure chainedGuards(x: int)
  returns (r: int)
{
  if x > 10
    then {
      {
        r := 1;
        exit $return
      }
    };
  if x > 5
    then {
      {
        r := 2;
        exit $return
      }
    };
  {
    r := 3;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(x: int): int
  opaque;
procedure chainedGuards(x: int)
  returns (r: int)
{
  var r: int := $declHole_3(x);
  if x > 10
    then {
      var r: int := 1;
      r
    }
    else if x > 5
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
#eval printRewritten
#strata
program Laurel;
procedure chainedGuards(x: int) returns (r: int) {
  if x > 10 then {
    return 1
  };
  if x > 5 then {
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
info: -- before --
procedure deadCodeAfterIfElse(b: bool)
  returns (r: int)
{
  if b
    then {
      {
        r := 1;
        exit $return
      }
    }
    else {
      {
        r := 2;
        exit $return
      }
    };
  {
    r := 3;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(b: bool): int
  opaque;
procedure deadCodeAfterIfElse(b: bool)
  returns (r: int)
{
  var r: int := $declHole_3(b);
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
#eval printRewritten
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
info: -- before --
procedure nestedIf(x: int)
  returns (r: int)
{
  if x > 0
    then {
      if x > 10
        then {
          {
            r := 1;
            exit $return
          }
        }
        else {
          {
            r := 2;
            exit $return
          }
        }
    }
    else {
      {
        r := 3;
        exit $return
      }
    }
}$return;
-- after --
procedure $declHole_3(x: int): int
  opaque;
procedure nestedIf(x: int)
  returns (r: int)
{
  var r: int := $declHole_3(x);
  if x > 0
    then if x > 10
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
#eval printRewritten
#strata
program Laurel;
procedure nestedIf(x: int) returns (r: int) {
  if x > 0 then {
    if x > 10 then {
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
info: -- before --
procedure nestedGuard(x: int, y: int)
  returns (r: int)
{
  if x > 0
    then {
      if y > 0
        then {
          {
            r := 1;
            exit $return
          }
        }
    };
  {
    r := 2;
    exit $return
  }
}$return;
-- after --
procedure $declHole_4(x: int, y: int): int
  opaque;
procedure nestedGuard(x: int, y: int)
  returns (r: int)
{
  var r: int := $declHole_4(x, y);
  if x > 0
    then if y > 0
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
#eval printRewritten
#strata
program Laurel;
procedure nestedGuard(x: int, y: int) returns (r: int) {
  if x > 0 then {
    if y > 0 then {
      return 1
    }
  };
  return 2
};
#end

/-! ## A destructive update becomes a shadowing declaration

`x := x + 1` turns into a second `var x` nested inside the scope of the first.
Shadowing is legal because `Resolution.defineNameCheckDup` is per-scope and the
declaration goes in a fresh block, and the update still reads the previous
binding because the initializer resolves in the *enclosing* scope.
`InlineLocalVariables` then inlines both declarations away. -/

/--
info: -- before --
procedure updateLocal(a: int)
  returns (r: int)
{
  var x: int := a;
  x := x + 1;
  {
    r := x;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(a: int): int
  opaque;
procedure updateLocal(a: int)
  returns (r: int)
{
  var r: int := $declHole_3(a);
  {
    var $v_4: int := a;
    {
      var $v_4: int := $v_4 + 1;
      {
        var r: int := $v_4;
        r
      }
    }
  }
};
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure updateLocal(a: int) returns (r: int) {
  var x: int := a;
  x := x + 1;
  return x
};
#end

/-! ## An if that assigns a local in both branches needs no if-lifting

Each branch becomes `{ var x := ...; <continuation> }`, so the assignment and
the code that reads it end up in the same branch. Inlining collapses them
afterwards. There is no restriction on how many variables a branch assigns. -/

/--
info: -- before --
procedure ifAssignsLocal(b: bool, a: int)
  returns (r: int)
{
  var x: int := 0;
  if b
    then {
      x := a + 1
    }
    else {
      x := a
    };
  {
    r := x;
    exit $return
  }
}$return;
-- after --
procedure $declHole_4(b: bool, a: int): int
  opaque;
procedure ifAssignsLocal(b: bool, a: int)
  returns (r: int)
{
  var r: int := $declHole_4(b, a);
  {
    var $v_5: int := 0;
    if b
      then {
        var $v_5: int := a + 1;
        {
          var r: int := $v_5;
          r
        }
      }
      else {
        var $v_5: int := a;
        {
          var r: int := $v_5;
          r
        }
      }
  }
};
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure ifAssignsLocal(b: bool, a: int) returns (r: int) {
  var x: int := 0;
  if b then {
    x := a + 1
  } else {
    x := a
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
info: -- before --
procedure exitSkipsRest(x: int)
  returns (r: int)
{
  var y: int := 0;
  {
    if x > 0
      then {
        y := 1;
        exit done
      };
    y := 2
  }done;
  {
    r := y;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(x: int): int
  opaque;
procedure exitSkipsRest(x: int)
  returns (r: int)
{
  var r: int := $declHole_3(x);
  {
    var $v_4: int := 0;
    if x > 0
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
#eval printRewritten
#strata
program Laurel;
procedure exitSkipsRest(x: int) returns (r: int) {
  var y: int := 0;
  {
    if x > 0 then {
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
info: -- before --
procedure exitToLabel(x: int)
  returns (r: int)
{
  {
    if x > 0
      then {
        exit done
      };
    {
      r := 1;
      exit $return
    }
  }done
}$return;
-- after --
procedure $declHole_3(x: int): int
  opaque;
procedure exitToLabel(x: int)
  returns (r: int)
{
  var r: int := $declHole_3(x);
  if x > 0
    then r
    else {
      var r: int := 1;
      r
    }
};
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure exitToLabel(x: int) returns (r: int) {
  {
    if x > 0 then {
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
info: -- before --
procedure labelledBlockNotLast(x: int)
  returns (r: int)
{
  {
    r := 1
  }done;
  {
    r := 2;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(x: int): int
  opaque;
procedure labelledBlockNotLast(x: int)
  returns (r: int)
{
  var r: int := $declHole_3(x);
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
#eval printRewritten
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
info: -- before --
procedure blockValued(a: int)
  returns (r: int)
{
  r := {
    var y: int := a;
    y := y + 1;
    y
  };
  {
    r := r;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(a: int): int
  opaque;
procedure blockValued(a: int)
  returns (r: int)
{
  var r: int := $declHole_3(a);
  {
    var r: int := {
      var $v_4: int := a;
      {
        var $v_4: int := $v_4 + 1;
        $v_4
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
#eval printRewritten
#strata
program Laurel;
procedure blockValued(a: int) returns (r: int) {
  r := { var y: int := a; y := y + 1; y };
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

The later `x := a + 1` becomes a *shadowing* declaration nested inside, exactly as
any other assignment does, so the hole is only what `x` holds before that
assignment — here, nothing reads it. Binding unconditionally rather than dropping
the declaration is what makes the rewrite sound: a dropped declaration leaves a
free reference on any path that never assigns, and if the name shadows an input
parameter that reference silently resolves to the input. -/

/--
info: -- before --
procedure uninitThenAssign(a: int)
  returns (r: int)
{
  var x: int;
  x := a + 1;
  {
    r := x;
    exit $return
  }
}$return;
-- after --
procedure $declHole_3(a: int): int
  opaque;
procedure $declHole_4(a: int): int
  opaque;
procedure uninitThenAssign(a: int)
  returns (r: int)
{
  var r: int := $declHole_3(a);
  {
    var $declHoleVal_4: int := $declHole_4(a);
    {
      var $v_4: int := $declHoleVal_4;
      {
        var $v_4: int := a + 1;
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
#eval printRewritten
#strata
program Laurel;
procedure uninitThenAssign(a: int) returns (r: int) {
  var x: int;
  x := a + 1;
  return x
};
#end

/-! ### A local that is never assigned at all

Nothing shadows the hole here, so the body evaluates to it directly: the function
returns an arbitrary-but-fixed value. It is *fixed* rather than arbitrary-per-call
because the hole is an uninterpreted function, which is what lets a transparent body
stay a function; with no inputs to depend on, this one is nullary. -/

/--
info: -- before --
procedure uninitRead()
  returns (r: int)
{
  var x: int;
  {
    r := x;
    exit $return
  }
}$return;
-- after --
procedure $declHole_2(): int
  opaque;
procedure $declHole_3(): int
  opaque;
procedure uninitRead()
  returns (r: int)
{
  var r: int := $declHole_2();
  {
    var $declHoleVal_3: int := $declHole_3();
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
#eval printRewritten
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
info: -- before --
procedure valueless(x: int)
{
  if x > 0
    then {
      exit $return
    };
  exit $return
}$return;
-- after --
procedure valueless(x: int)
{
  if x > 0
    then {
      exit $return
    };
  exit $return
}$return;
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure valueless(x: int) {
  if x > 0 then {
    return
  };
  return
};
#end

/-! ## Bodies with no functional form are reported, and left untouched

In each case below the `-- after --` output equals the `-- before --` output:
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
info: -- before --
procedure hasLoop(n: int)
  returns (r: int)
{
  var i: int := 0;
  while(i < n) {
    i := i + 1
  };
  {
    r := i;
    exit $return
  }
}$return;
-- after --
procedure hasLoop(n: int)
  returns (r: int)
{
  var i: int := 0;
  while(i < n) {
    i := i + 1
  };
  {
    r := i;
    exit $return
  }
}$return;
diagnostic[userError]: loops are not YET supported in transparent bodies or contracts
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure hasLoop(n: int) returns (r: int) {
  var i: int := 0;
  while (i < n) {
    i := i + 1
  };
  return i
};
#end

/-! ### An assert -/

/--
info: -- before --
procedure hasAssert(x: int)
  returns (r: int)
{
  assert x > 0;
  {
    r := x;
    exit $return
  }
}$return;
-- after --
procedure hasAssert(x: int)
  returns (r: int)
{
  assert x > 0;
  {
    r := x;
    exit $return
  }
}$return;
diagnostic[error]: assert should have been stripped from the function copy by the transparency pass
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure hasAssert(x: int) returns (r: int) {
  assert x > 0;
  return x
};
#end

/-! ### An assume -/

/--
info: -- before --
procedure hasAssume(x: int)
  returns (r: int)
{
  assume x > 0;
  {
    r := x;
    exit $return
  }
}$return;
-- after --
procedure hasAssume(x: int)
  returns (r: int)
{
  assume x > 0;
  {
    r := x;
    exit $return
  }
}$return;
diagnostic[error]: assume should have been stripped from the function copy by the transparency pass
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure hasAssume(x: int) returns (r: int) {
  assume x > 0;
  return x
};
#end

/-! ### An assignment to an input parameter

This is a destructive assignment the Core translator must keep rejecting.
Turning it into a shadowing declaration would silently accept the program, so
input names are checked before the binding rule applies. -/

/--
info: -- before --
procedure assignsInput(a: int)
  returns (r: int)
{
  a := a + 1;
  {
    r := a;
    exit $return
  }
}$return;
-- after --
procedure assignsInput(a: int)
  returns (r: int)
{
  a := a + 1;
  {
    r := a;
    exit $return
  }
}$return;
diagnostic[userError]: destructive assignments are not supported in transparent bodies or contracts
-/
#guard_msgs in
#eval printRewritten
#strata
program Laurel;
procedure assignsInput(a: int) returns (r: int) {
  a := a + 1;
  return a
};
#end

/-! ### More than one output

A function evaluates to a single value, so there is no way for one to yield
several outputs at once. This needs a tuple construct in Laurel, or a real
`let` in Core. -/

/--
info: -- before --
procedure twoOuts()
  returns (q: int, r: int)
{
  q := 1;
  r := 2
}$return;
-- after --
procedure twoOuts()
  returns (q: int, r: int)
{
  q := 1;
  r := 2
}$return;
diagnostic[userError]: a transparent body with 2 output parameters is not supported; it must have at most one
-/
#guard_msgs in
#eval printRewritten
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
info: -- before --
procedure callee()
  returns (r: int)
{
  {
    r := 1;
    exit $return
  }
}$return;
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
-- after --
procedure $declHole_3(): int
  opaque;
procedure callee()
  returns (r: int)
{
  var r: int := $declHole_3();
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
diagnostic[error]: call should have been rewritten to functional form by the transparency pass
-/
#guard_msgs in
#eval printRewritten
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
