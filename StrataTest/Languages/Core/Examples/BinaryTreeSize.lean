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

// Safe accessors for IntList
inline function head(xs : IntList) : int
  requires IntList..isCons(xs);
{ IntList..hd(xs) }

inline function tail(xs : IntList) : IntList
  requires IntList..isCons(xs);
{ IntList..tl(xs) }

// Safe accessors for IntTree
inline function left(t : IntTree) : IntTree
  requires IntTree..isNode(t);
{ IntTree..left(t) }

inline function right(t : IntTree) : IntTree
  requires IntTree..isNode(t);
{ IntTree..right(t) }

inline function val(t : IntTree) : int
  requires IntTree..isNode(t);
{ IntTree..val(t) }

recursive function listLen (xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(tail(xs))
}

recursive function append (xs : IntList, ys : IntList) : IntList
  decreases xs
{
  if IntList..isNil(xs) then ys
  else Cons(head(xs), append(tail(xs), ys))
}

recursive function size (t : IntTree) : int
  decreases t
{
  if IntTree..isLeaf(t) then 0
  else 1 + size(left(t)) + size(right(t))
}

recursive function toList (t : IntTree) : IntList
  decreases t
{
  if IntTree..isLeaf(t) then Nil()
  else append(toList(left(t)), Cons(val(t), toList(right(t))))
}

// listLen distributes over append.
procedure LenAppend(xs : IntList, ys : IntList) returns ()
spec {
  ensures [len_append]: listLen(append(xs, ys)) == listLen(xs) + listLen(ys);
}
{
  if (IntList..isCons(xs))
  {
    call LenAppend(tail(xs), ys);
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
    call SizeIsLen(left(t));
    call SizeIsLen(right(t));
    call LenAppend(toList(left(t)), Cons(val(t), toList(right(t))));
  }
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram sizeIsLenPgm) |>.snd |>.isEmpty

/--
info:
Obligation: listLen_body_calls_tail_0
Property: assert
Result: ✅ pass

Obligation: append_body_calls_head_0
Property: assert
Result: ✅ pass

Obligation: append_body_calls_tail_1
Property: assert
Result: ✅ pass

Obligation: size_body_calls_left_0
Property: assert
Result: ✅ pass

Obligation: size_body_calls_right_1
Property: assert
Result: ✅ pass

Obligation: toList_body_calls_left_0
Property: assert
Result: ✅ pass

Obligation: toList_body_calls_val_1
Property: assert
Result: ✅ pass

Obligation: toList_body_calls_right_2
Property: assert
Result: ✅ pass

Obligation: call_LenAppend_arg_calls_tail_0
Property: assert
Result: ✅ pass

Obligation: len_append
Property: assert
Result: ✅ pass

Obligation: call_SizeIsLen_arg_calls_left_0
Property: assert
Result: ✅ pass

Obligation: call_SizeIsLen_arg_calls_right_0
Property: assert
Result: ✅ pass

Obligation: call_LenAppend_arg_calls_left_0
Property: assert
Result: ✅ pass

Obligation: call_LenAppend_arg_calls_val_0
Property: assert
Result: ✅ pass

Obligation: call_LenAppend_arg_calls_right_1
Property: assert
Result: ✅ pass

Obligation: size_is_len
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sizeIsLenPgm (options := .quiet)

end Strata.BinaryTreeSizeTest
