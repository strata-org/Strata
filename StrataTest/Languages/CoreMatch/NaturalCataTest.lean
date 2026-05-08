/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CoreMatch.CoreMatch
import Strata.Languages.CoreMatch.ToCore
import Strata.Languages.CoreMatch.DDMTransform.Translate.NaturalCata
import Strata.Languages.CoreMatch.Verify
import Strata.Languages.CoreMatch.DDMTransform.StrataGen

/-!
Tests for the natural-style to cata-style desugaring. Combines direct
unit tests on the helpers in
`CoreMatch.DDMTransform.Translate.NaturalCata` with end-to-end
property checks confirming that natural-style and cata-style source
programs lower to identical Core expressions.
-/

open Strata Strata.CoreMatch Strata.CoreMatch.Translate
open Lambda

namespace CoreMatchNaturalCataTest


/-! Sentinel naming -/

#guard recSentinelName 0 == "$$coreMatch$rec$0"
#guard recSentinelName 1 == "$$coreMatch$rec$1"
#guard recSentinelName 7 == "$$coreMatch$rec$7"

-- Sentinel names are unguessable — `$$` prefix never appears in a
-- valid CoreMatch identifier.
#guard (recSentinelName 0).startsWith "$$coreMatch"


/-! `naturalRecRewrites` shape

Test the bookkeeping that drives `tryRecRewrite`: keys are
`(fnName, baseDepth + fieldIdx)`, values are slot indices counted
from `recCount - 1` down to 0 in declaration order. -/

-- Single recursive field, single rec function: one entry, slot 0.
#guard naturalRecRewrites ["length"] [1] 0
       == [(("length", 1), 0)]

-- Two recursive fields (binary tree `Node(value, left, right)` →
-- recIdxs = [1, 2]), one rec function: two entries, slots reversed
-- (left → 1, right → 0) so `right_rec` ends up at innermost
-- bvar 0 in the case lambda.
#guard naturalRecRewrites ["treeSum"] [1, 2] 0
       == [(("treeSum", 1), 1), (("treeSum", 2), 0)]

-- Three recursive fields: slot indices recCount-1 down to 0.
#guard naturalRecRewrites ["f"] [0, 1, 2] 0
       == [(("f", 0), 2), (("f", 1), 1), (("f", 2), 0)]

-- Non-zero baseDepth shifts every key by the same amount.
#guard naturalRecRewrites ["length"] [1] 5
       == [(("length", 6), 0)]

-- Mutually recursive functions: each rec field appears once per
-- function, so two rec fns × two rec fields = four entries.
#guard naturalRecRewrites ["f", "g"] [0, 1] 0
       == [(("f", 0), 1), (("f", 1), 0),
           (("g", 0), 1), (("g", 1), 0)]

-- No rec functions in scope ⇒ no entries even with rec fields.
#guard naturalRecRewrites [] [0, 1] 0 == []

-- No rec fields ⇒ no entries even with rec functions.
#guard naturalRecRewrites ["f"] [] 0 == []


/-! `desugarNaturalToCata` mechanics

The transformation is pure: given `(resultType, recCount, binders,
body-with-sentinels)`, returns `(extendedBinders, body-with-bvars)`.
The injected binders are named `rec_0..rec_{n-1}`, typed as the
function's return type, and appended to the user's binders. -/

-- recCount = 0 is a no-op (cata/unknown shape would skip the call,
-- but the function should still be safe to invoke).
#guard let (b, _) := desugarNaturalToCata .int 0 [("hd", .int)] (.intConst () 0)
       b == [("hd", .int)]

-- recCount = 1: appends one rec_0 binder.
#guard let (b, _) := desugarNaturalToCata .int 1 [("tl", .tcons "List" [])]
                                          (.intConst () 0)
       b == [("tl", .tcons "List" []), ("rec_0", .int)]

-- recCount = 2: appends rec_0 and rec_1 in order.
#guard let (b, _) := desugarNaturalToCata .int 2
                       [("left", .tcons "Tree" []), ("right", .tcons "Tree" [])]
                       (.intConst () 0)
       b == [("left", .tcons "Tree" []), ("right", .tcons "Tree" []),
             ("rec_0", .int), ("rec_1", .int)]

-- The injected binders are typed as the *result* type, regardless of
-- the user binders' types.
#guard let (b, _) := desugarNaturalToCata .bool 1 [] (.intConst () 0)
       b == [("rec_0", .bool)]


/-! Sentinel substitution

The body's sentinels become bvars; the existing bvars are lifted
past the new injection. -/

-- A body that's a single sentinel: should resolve to bvar 0.
#guard let (_, body) := desugarNaturalToCata .int 1 []
                          (.fvar () ⟨recSentinelName 0, ()⟩ none)
       body matches .bvar _ 0

-- Two sentinels, ordered by slot index.
#guard let (_, body) := desugarNaturalToCata .int 2 []
                          (.app () (.fvar () ⟨recSentinelName 0, ()⟩ none)
                                   (.fvar () ⟨recSentinelName 1, ()⟩ none))
       match body with
       | .app _ (.bvar _ 0) (.bvar _ 1) => true
       | _ => false

-- A pre-existing bvar in the body gets lifted by recCount.  Setup:
-- one user binder `hd` referenced as bvar 0, then recCount = 1
-- injection.  Expected: bvar 0 → bvar 1.
#guard let (_, body) := desugarNaturalToCata .int 1 [("hd", .int)]
                          (.bvar () 0)
       body matches .bvar _ 1

-- recCount = 2 lift: bvar 0 → bvar 2, bvar 1 → bvar 3.
#guard let (_, body) := desugarNaturalToCata .int 2
                          [("hd", .int), ("tl", .tcons "List" [])]
                          (.app () (.bvar () 1) (.bvar () 0))
       match body with
       | .app _ (.bvar _ 3) (.bvar _ 2) => true
       | _ => false


/-! End-to-end: natural and cata produce identical Core

The strongest property: source programs that differ only in
natural-vs-cata style lower to byte-identical Core. -/

-- Helper: extract the body of the named function from a parsed program.
private def fnBody (p : Strata.Program) (name : String) : Option Core.Expression.Expr :=
  match Strata.CoreMatch.Verify.parseToCore p "test" with
  | .error _ => none
  | .ok prog =>
    prog.decls.findSome? fun
      | .func f _ => if f.name.name == name then f.body else none
      | _ => none

private def pListNatural : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function length(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + length(tl);
  }
};
#end

private def pListCata : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

function length(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List, lenTl : int) => 1 + lenTl;
  }
};
#end

-- Both styles produce a body, both bodies are equal.
#guard fnBody pListNatural "length" |>.isSome
#guard fnBody pListCata "length" |>.isSome
#guard fnBody pListNatural "length" == fnBody pListCata "length"


/-! Multiple recursive fields

Binary tree DFS: `Node(value, left, right)` → two rec-result binders
in declaration order at the *end* of the case-lambda binder list. -/

private def pTreeNatural : Strata.Program :=
#strata
program CoreMatch;

datatype Tree () { Leaf(), Node(value : int, left : Tree, right : Tree) };

rec function treeSum(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree) =>
      value + treeSum(left) + treeSum(right);
  }
};
#end

private def pTreeCata : Strata.Program :=
#strata
program CoreMatch;

datatype Tree () { Leaf(), Node(value : int, left : Tree, right : Tree) };

function treeSum(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree, leftR : int, rightR : int) =>
      value + leftR + rightR;
  }
};
#end

#guard fnBody pTreeNatural "treeSum" |>.isSome
#guard fnBody pTreeCata "treeSum" |>.isSome
#guard fnBody pTreeNatural "treeSum" == fnBody pTreeCata "treeSum"


/-! Mutually recursive functions

Both functions in the block are eligible self-call targets. -/

private def pMutual : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function length(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + length(tl);
  }
};

rec function sum(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => hd + sum(tl);
  }
};
#end

#guard fnBody pMutual "length" |>.isSome
#guard fnBody pMutual "sum" |>.isSome


/-! Non-structural recursion is rejected

The natural-style rewrite only fires for `f(field)` where `field`
is a recursive constructor field of the enclosing match.  All other
forms reject. -/

private def parseError? (p : Strata.Program) : Bool :=
  match Strata.CoreMatch.Verify.parseToCore p "test" with
  | .ok _    => false
  | .error _ => true

-- f(non-recursive-field-of-other-binder).
private def pBadOtherParam : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function bad(xs : List, ys : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + bad(ys, tl);
  }
};
#end

#guard parseError? pBadOtherParam

-- f passed as a value (no argument applied).  Note: this won't even
-- type-check at the source level since `f` has function type, but
-- it confirms the .fvar branch in toCoreExpr would reject it.
private def pBadValue : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function badValue(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + badValue(xs);
  }
};
#end

-- xs is the function input, not a recursive *field*; rejected.
#guard parseError? pBadValue


/-! Wrong binder count is rejected with a clear error

Neither natural (== fc) nor cata (== fc + recCount) shape ⇒ classify
fails. -/

private def pWrongArity : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

function bad(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int) => hd;
  }
};
#end

-- Cons has 2 fields; user wrote 1 binder.  Expected: 2 or 3 (cata
-- with one rec-result), got 1.  Reject.
#guard parseError? pWrongArity


end CoreMatchNaturalCataTest
