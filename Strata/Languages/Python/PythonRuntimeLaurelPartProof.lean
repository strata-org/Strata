/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
public import Strata.Languages.Laurel.Laurel

namespace Strata
namespace Python

/--
Python prelude declarations expressed in Laurel grammar.
Converted from PythonLaurelCorePrelude.lean (Core dialect) to Laurel dialect.

Core-specific constructs that Laurel does not support:
- `inline` keyword: noted in comments
- Labels on requires/ensures/assert/assume: noted in nearby comments
- Axioms: commented out
- `mutual`/`end` blocks: flattened (Laurel does not support mutual blocks)
-/
private def pythonRuntimeLaurelPartProofDDM :=
#strata
program Laurel;

procedure List_extend_len(l1 : ListAny, l2: ListAny)
  invokeOn List_len(List_extend(l1,l2))
  opaque
  ensures List_len(List_extend(l1,l2)) == List_len(l1) + List_len(l2);

procedure List_take_get(l : ListAny, i: int, j: int)
  invokeOn List_get(List_take(l, i), j)
  opaque
  ensures if 0 <= i && i <= List_len(l) && 0 <= j && j < List_len(l) && j < i then
        List_get(List_take(l, i), j) == List_get(l,j) else true;

procedure List_drop_get(l : ListAny, i: int, j: int)
  invokeOn List_get(List_drop(l, i), j)
  opaque
  ensures if 0 <= i && i <= List_len(l) && 0 <= j && j < List_len(l) - i then
        List_get(List_drop(l, i), j) == List_get(l,j + i) else true;


procedure List_extend_get_1(l1 : ListAny, l2: ListAny, i: int)
  invokeOn List_get(List_extend(l1, l2), i)
  opaque
  ensures if 0 <= i && i < List_len(l1) then
          List_get(List_extend(l1, l2), i) == List_get(l1,i) else true;

procedure List_extend_get_2(l1 : ListAny, l2: ListAny, i: int)
  invokeOn List_get(List_extend(l1, l2), i)
  opaque
  ensures if List_len(l1) <= i && i < List_len(l1) + List_len(l2) then
          List_get(List_extend(l1, l2), i) == List_get(l2, i - List_len(l1)) else true;


procedure List_remove_non_neg_length (l: ListAny, i:int) returns ()
  opaque
{
  assert  if 0 <= i && i < List_len(l) then List_len(List_remove_non_neg(l, i)) == List_len(l) - 1
          else true summary "List_remove_non_neg_length"
};

procedure List_remove_non_neg_get (l: ListAny, i:int, j: int) returns ()
  opaque
{
  assert if 0 <= i && i < List_len(l) && 0 <= j && j < List_len(l) - 1 then
    List_get(List_remove_non_neg(l, i), j) ==
          (if j < i then List_get(l, j) else List_get(l, j + 1))
    else true summary "List_remove_non_neg_get"
};

procedure List_remove_roundtrip (l: ListAny, i:int) returns ()
  opaque
{
  assert  if 0 <= i && i < List_len(l) then List_remove_non_neg(l, i) == List_remove_slice(l, i, i + 1)
          else true summary "List_remove_roundtrip"
};


procedure List_remove_slice_length (l: ListAny, start: int, stop: int) returns ()
  opaque
{
  var start_c : int := if start >= 0 then int_min(start, List_len(l)) else int_max(List_len(l) + start, 0);
  var stop_c : int := if stop >= 0 then int_min(stop, List_len(l)) else int_max(List_len(l) + stop, 0);
  assert  List_len(List_remove_slice(l, start, stop)) ==
            if start_c >= stop_c then List_len(l)
            else List_len(l) - (stop_c - start_c) summary "List_remove_slice_length"
};


#end

public def pythonRuntimeLaurelPartProof : Laurel.Program :=
  match Laurel.TransM.run (some $ .file "") (Laurel.parseProgram pythonRuntimeLaurelPartProofDDM) with
  | .ok p => p
  | .error e => dbg_trace s!"SOUND BUG: Failed to parse Python runtime Laurel part: {e}"; default


end Python
end Strata
