/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Binary Tree Size Test

Proves that `size(t) == listLen(toList(t))` for all binary trees `t`,
using a recursive procedure whose contract states the equivalence.
The recursive calls on subtrees provide the inductive hypotheses.
-/

namespace Strata.BinaryTreeSizeTest

def sizeIsLenPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
datatype IntTree { Leaf(), Node(left: IntTree, val: int, right: IntTree) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

rec function append (@[cases] xs : IntList, ys : IntList) : IntList
{
  if IntList..isNil(xs) then ys
  else Cons(IntList..hd(xs), append(IntList..tl(xs), ys))
};

rec function size (@[cases] t : IntTree) : int
{
  if IntTree..isLeaf(t) then 0
  else 1 + size(IntTree..left(t)) + size(IntTree..right(t))
};

rec function toList (@[cases] t : IntTree) : IntList
{
  if IntTree..isLeaf(t) then Nil()
  else append(toList(IntTree..left(t)), Cons(IntTree..val(t), toList(IntTree..right(t))))
};

// listLen distributes over append.
procedure LenAppend(xs : IntList, ys : IntList) returns ()
spec {
  ensures [len_append]: listLen(append(xs, ys)) == listLen(xs) + listLen(ys);
}
{
  if (IntList..isCons(xs))
  {
    call LenAppend(IntList..tl(xs), ys);
  }
};

// Main theorem: size(t) == listLen(toList(t))
procedure SizeIsLen(t : IntTree) returns ()
spec {
  ensures [size_is_len]: size(t) == listLen(toList(t));
}
{
  if (IntTree..isNode(t))
  {
    call SizeIsLen(IntTree..left(t));
    call SizeIsLen(IntTree..right(t));
    call LenAppend(toList(IntTree..left(t)), Cons(IntTree..val(t), toList(IntTree..right(t))));
  }
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram sizeIsLenPgm) |>.snd |>.isEmpty

/--
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: append_terminates_0
Property: assert
Result: ✅ pass

Obligation: append_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: append_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: size_terminates_0
Property: assert
Result: ✅ pass

Obligation: size_terminates_1
Property: assert
Result: ✅ pass

Obligation: size_body_calls_IntTree..left_0
Property: assert
Result: ✅ pass

Obligation: size_body_calls_IntTree..right_1
Property: assert
Result: ✅ pass

Obligation: toList_terminates_0
Property: assert
Result: ✅ pass

Obligation: toList_terminates_1
Property: assert
Result: ✅ pass

Obligation: toList_body_calls_IntTree..left_0
Property: assert
Result: ✅ pass

Obligation: toList_body_calls_IntTree..val_1
Property: assert
Result: ✅ pass

Obligation: toList_body_calls_IntTree..right_2
Property: assert
Result: ✅ pass

Obligation: init_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: len_append
Property: assert
Result: ✅ pass

Obligation: init_calls_IntTree..left_0
Property: assert
Result: ✅ pass

Obligation: init_calls_IntTree..right_0
Property: assert
Result: ✅ pass

Obligation: init_calls_IntTree..left_0
Property: assert
Result: ✅ pass

Obligation: init_calls_IntTree..val_0
Property: assert
Result: ✅ pass

Obligation: init_calls_IntTree..right_1
Property: assert
Result: ✅ pass

Obligation: size_is_len
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sizeIsLenPgm (options := .quiet)

end Strata.BinaryTreeSizeTest
