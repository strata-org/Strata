/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.CommonSubexprElim
meta import Strata.Transform.CoreTransform
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.SimpleAPI
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! ## Common-subexpression-elimination large / stress test

`gen_12` chains twelve heap updates (`$heap := increment($heap)` /
`modifyOne$asFunction`). After symbolic evaluation the `$heap` term is a small
DAG, but because `increment` references its argument twice its *tree* unfolding
is `O(2^depth)`. A non-memoized CSE pass therefore blows up exponentially
(seconds, then minutes as the chain grows).

This test runs the real pre-CSE pipeline (type check + symbolic evaluation, via
`typeCheckAndBuildObligationProgram`, which stops just before CSE) and then runs
CSE on the resulting obligation program. It guards two things:

* Performance: the transform must stay linear in the number of distinct DAG
  nodes. If it regresses to the exponential tree walk, elaborating this file
  (which evaluates the `#guard`s below) will hang.
* Correctness: CSE extracts the expected number of `$__cse.` variables and
  reports that it changed the program. -/

namespace Core.CSE.LargeTests

open Strata Core Core.Transform Core.CSE

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def gen12Prog :=
#strata
program Core;

datatype TypeTag {
  Container_TypeTag()
};
datatype Field {
  Container.value()
};
datatype Box {
  BoxInt(intVal : int)
};
datatype Composite {
  MkComposite(ref : int, typeTag : TypeTag)
};
datatype NotSupportedYet {
  MkNotSupportedYet()
};
datatype Heap {
  MkHeap(data : Map Composite (Map Field Box), nextReference : int)
};
datatype LaurelResolutionErrorPlaceholder {
  MkLaurelResolutionErrorPlaceholder()
};
datatype Float64IsNotSupportedYet {
  MkFloat64IsNotSupportedYet()
};
datatype LaurelUnit {
  MkLaurelUnit()
};
function ancestorsForContainer () : Map TypeTag bool {
  (mapConst<TypeTag>(false))[Container_TypeTag:=true]
}
function ancestorsPerType () : Map TypeTag (Map TypeTag bool) {
  (mapConst<TypeTag>(mapConst<TypeTag>(false)))[Container_TypeTag:=ancestorsForContainer]
}
function modifyOne$post0 ($heap : Heap, c : Composite, $heap$out : Heap) : bool {
  Heap..data!($heap$out) == (Heap..data!($heap))[c:=(Heap..data!($heap$out))[c]] && int.le(Heap..nextReference!($heap), Heap..nextReference!($heap$out))
}
function readField (heap : Heap, obj : Composite, field : Field) : Box {
  ((Heap..data!(heap))[obj])[field]
}
function modifyOne$post1 ($heap : Heap, c : Composite, $heap$out : Heap) : bool {
  forall $modifies_obj : Composite :: forall $modifies_fld : Field :: (if int.lt(Composite..ref!($modifies_obj), Heap..nextReference!($heap)) && !($modifies_obj == c) then readField($heap, $modifies_obj, $modifies_fld) == readField($heap$out, $modifies_obj, $modifies_fld) else true)
}
function updateField (heap : Heap, obj : Composite, field : Field, val : Box) : Heap {
  MkHeap((Heap..data!(heap))[obj:=((Heap..data!(heap))[obj])[field:=val]], Heap..nextReference!(heap))
}
function increment (heap : Heap) : Heap {
  MkHeap(Heap..data!(heap), int.add(Heap..nextReference!(heap), 1))
}
function modifyOne$asFunction ($heap : Heap, c : Composite) : Heap;
function stress$asFunction ($heap : Heap) : Heap;
procedure modifyOne (inout $heap : Heap, c : Composite)
{
  assume [assume_true]: true;
};
procedure stress (inout $heap : Heap)
{
  $return: {
    var $th_tmp0 : int := Heap..nextReference!($heap);
    var $$heap_0 : Heap := $heap;
    $heap := increment($heap);
    var target : Composite := MkComposite($th_tmp0, Container_TypeTag);
    var x : int := Box..intVal!(readField($heap, target, Container.value));
    var $th_tmp1 : int := Heap..nextReference!($heap);
    var $$heap_1 : Heap := $heap;
    $heap := increment($heap);
    var c0 : Composite := MkComposite($th_tmp1, Container_TypeTag);
    var $cp_2 : Heap := $heap;
    var $cp_3 : Composite := c0;
    $heap := modifyOne$asFunction($heap, $cp_3);
    assume [|assume(1075)|]: modifyOne$post0($cp_2, $cp_3, $heap);
    var $th_tmp2 : int := Heap..nextReference!($heap);
    var $$heap_2 : Heap := $heap;
    $heap := increment($heap);
    var c1 : Composite := MkComposite($th_tmp2, Container_TypeTag);
    var $cp_4 : Heap := $heap;
    var $cp_5 : Composite := c1;
    $heap := modifyOne$asFunction($heap, $cp_5);
    assume [|assume(1128)|]: modifyOne$post0($cp_4, $cp_5, $heap);
    var $th_tmp3 : int := Heap..nextReference!($heap);
    var $$heap_3 : Heap := $heap;
    $heap := increment($heap);
    var c2 : Composite := MkComposite($th_tmp3, Container_TypeTag);
    var $cp_6 : Heap := $heap;
    var $cp_7 : Composite := c2;
    $heap := modifyOne$asFunction($heap, $cp_7);
    assume [|assume(1181)|]: modifyOne$post0($cp_6, $cp_7, $heap);
    var $th_tmp4 : int := Heap..nextReference!($heap);
    var $$heap_4 : Heap := $heap;
    $heap := increment($heap);
    var c3 : Composite := MkComposite($th_tmp4, Container_TypeTag);
    var $cp_8 : Heap := $heap;
    var $cp_9 : Composite := c3;
    $heap := modifyOne$asFunction($heap, $cp_9);
    assume [|assume(1234)|]: modifyOne$post0($cp_8, $cp_9, $heap);
    var $th_tmp5 : int := Heap..nextReference!($heap);
    var $$heap_5 : Heap := $heap;
    $heap := increment($heap);
    var c4 : Composite := MkComposite($th_tmp5, Container_TypeTag);
    var $cp_10 : Heap := $heap;
    var $cp_11 : Composite := c4;
    $heap := modifyOne$asFunction($heap, $cp_11);
    assume [|assume(1287)|]: modifyOne$post0($cp_10, $cp_11, $heap);
    var $th_tmp6 : int := Heap..nextReference!($heap);
    var $$heap_6 : Heap := $heap;
    $heap := increment($heap);
    var c5 : Composite := MkComposite($th_tmp6, Container_TypeTag);
    var $cp_12 : Heap := $heap;
    var $cp_13 : Composite := c5;
    $heap := modifyOne$asFunction($heap, $cp_13);
    assume [|assume(1340)|]: modifyOne$post0($cp_12, $cp_13, $heap);
    var $th_tmp7 : int := Heap..nextReference!($heap);
    var $$heap_7 : Heap := $heap;
    $heap := increment($heap);
    var c6 : Composite := MkComposite($th_tmp7, Container_TypeTag);
    var $cp_14 : Heap := $heap;
    var $cp_15 : Composite := c6;
    $heap := modifyOne$asFunction($heap, $cp_15);
    assume [|assume(1393)|]: modifyOne$post0($cp_14, $cp_15, $heap);
    var $th_tmp8 : int := Heap..nextReference!($heap);
    var $$heap_8 : Heap := $heap;
    $heap := increment($heap);
    var c7 : Composite := MkComposite($th_tmp8, Container_TypeTag);
    var $cp_16 : Heap := $heap;
    var $cp_17 : Composite := c7;
    $heap := modifyOne$asFunction($heap, $cp_17);
    assume [|assume(1446)|]: modifyOne$post0($cp_16, $cp_17, $heap);
    var $th_tmp9 : int := Heap..nextReference!($heap);
    var $$heap_9 : Heap := $heap;
    $heap := increment($heap);
    var c8 : Composite := MkComposite($th_tmp9, Container_TypeTag);
    var $cp_18 : Heap := $heap;
    var $cp_19 : Composite := c8;
    $heap := modifyOne$asFunction($heap, $cp_19);
    assume [|assume(1499)|]: modifyOne$post0($cp_18, $cp_19, $heap);
    var $th_tmp10 : int := Heap..nextReference!($heap);
    var $$heap_10 : Heap := $heap;
    $heap := increment($heap);
    var c9 : Composite := MkComposite($th_tmp10, Container_TypeTag);
    var $cp_20 : Heap := $heap;
    var $cp_21 : Composite := c9;
    $heap := modifyOne$asFunction($heap, $cp_21);
    assume [|assume(1552)|]: modifyOne$post0($cp_20, $cp_21, $heap);
    var $th_tmp11 : int := Heap..nextReference!($heap);
    var $$heap_11 : Heap := $heap;
    $heap := increment($heap);
    var c10 : Composite := MkComposite($th_tmp11, Container_TypeTag);
    var $cp_22 : Heap := $heap;
    var $cp_23 : Composite := c10;
    $heap := modifyOne$asFunction($heap, $cp_23);
    assume [|assume(1605)|]: modifyOne$post0($cp_22, $cp_23, $heap);
    var $th_tmp12 : int := Heap..nextReference!($heap);
    var $$heap_12 : Heap := $heap;
    $heap := increment($heap);
    var c11 : Composite := MkComposite($th_tmp12, Container_TypeTag);
    var $cp_24 : Heap := $heap;
    var $cp_25 : Composite := c11;
    $heap := modifyOne$asFunction($heap, $cp_25);
    assume [|assume(1658)|]: modifyOne$post0($cp_24, $cp_25, $heap);
    assert [|assert(2119)|]: x == Box..intVal!(readField($heap, target, Container.value));
  }
};
#end

/-- The obligation program CSE receives: type-checked and symbolically
    evaluated, but not yet common-subexpression-eliminated. -/
private def gen12Oblig : Core.Program :=
  match typeCheckAndBuildObligationProgram .quiet (translateCore gen12Prog) with
  | .ok (prog, _) => prog
  | .error e => panic! s!"obligation building failed: {e}"

/-- Run CSE on the obligation program. -/
private def gen12Cse : Bool × Core.Program :=
  match Core.Transform.run gen12Oblig Core.CSE.runCSE
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .ok res => res
  | .error e => panic! s!"CSE failed: {e}"

-- CSE changed the program (it lifted common subexpressions).
#guard gen12Cse.1

-- It extracted exactly 38 `$__cse.` var declarations. Counting the printed
-- `var $__cse.` prefixes (declarations, not references) also forces the whole
-- transform to run, which is the performance regression guard.
#guard (((toString gen12Cse.2).splitOn "var $__cse.").length - 1) = 38

/-! ## Many sequential path splits

`branchesProg n` is the program of `Examples/CSEPathSplits.core.st` with `n`
branches: a shared term `y` built by four steps of `y := y * y + y`, then `n`
sequential branches that each assume a fact about `y`, check `r == y` and leave
the block. Symbolic evaluation nests a block per branch, and every resulting
path repeats `y`. The test runs CSE on the obligation program and checks how
many `$__cse.` variables it introduces. The timing of the same program at 400
branches is checked by `StrataTestExtra/Transform/CommonSubexprElimScaling.lean`,
which runs the compiled CLI under `lake test`. -/

private def parseCore (text : String) : IO StrataDDM.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Strata.Core]
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"cse-branches-test"⟩ text
  StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx

/-- The program of `Examples/CSEPathSplits.core.st`, with `n` branches. -/
private def branchesProg (n : Nat) : String := Id.run do
  let mut lines := #[
    "procedure Dispatch(x : int, out y : int, out r : int)",
    "spec { ensures [r_is_y]: r == y; }",
    "{", "  y := x;"]
  for _ in [0:4] do
    lines := lines.push "  y := int.add(int.mul(y, y), y);"
  lines := lines.push "  done: {"
  for i in [0:n] do
    lines := lines.push s!"    if (x == {i}) \{ assume [a{i}]: int.ge(int.add(y, {i}), 0); \
      r := y; assert [b{i}]: r == y; exit done; }"
  lines := lines ++ #["    r := y;", "  }", "};"]
  return "\n".intercalate lines.toList

/-- The number of `$__cse.` declarations CSE put in the procedure bodies of `p`. -/
private def cseVarCount (p : Core.Program) : Nat :=
  p.decls.foldl (fun n d => match d with
    | .proc pr _ => match pr.body with
      | .structured ss => n + (ss.filter fun s => match s with
          | .cmd (.cmd (.init x _ _ _)) => Core.CSE.isCSEGeneratedName x.name
          | _ => false).length
      | _ => n
    | _ => n) 0

/-- The number of `$__cse.` variables CSE introduces on the obligation program of
    `branchesProg n`. -/
private def branchesCseVars (n : Nat) : IO Nat := do
  let oblig ← match typeCheckAndBuildObligationProgram .quiet
      (translateCore (← parseCore (branchesProg n))) with
    | .ok (prog, _) => pure prog
    | .error e => throw <| IO.userError s!"obligation building failed: {e}"
  match Core.Transform.run oblig Core.CSE.runCSE
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .ok (_, prog) => return cseVarCount prog
  | .error e => throw <| IO.userError s!"CSE failed: {e}"

/-- info: 63 -/
#guard_msgs in
#eval branchesCseVars 20

end Core.CSE.LargeTests
end
