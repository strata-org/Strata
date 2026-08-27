/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## Blocks are lexical scopes

A Laurel `{ ... }` block scopes its local declarations, so blocks whose scopes
do not overlap may reuse a name. A declaration is rejected only when the name is
already bound in an enclosing block still in scope, so an inner block cannot
shadow a name from an outer block; sibling and separately-nested blocks reuse
freely.
-/

#eval testLaurelVerification <|
#strata
program Laurel;

// Two sibling blocks each declare `t`: separate scopes, so the names do not
// collide.
procedure siblingBlocksReuseName()
  entry
  opaque
{
  {
    var t: int := 1;
    assert t == 1
  };
  {
    var t: int := 2;
    assert t == 2
  }
};

// A block-local declaration does not escape its block: reusing the name in the
// enclosing sequence after the block is a fresh binding.
procedure blockLocalDoesNotEscape()
  entry
  opaque
{
  {
    var t: int := 7;
    assert t == 7
  };
  var t: int := 9;
  assert t == 9
};

// Nested sibling blocks: an outer block wraps two inner blocks that each
// declare `t`. Each inner block has its own scope, so the two `t`s do not
// collide.
procedure nestedSiblingReuse()
  entry
  opaque
{
  {
    {
      var t: int := 1;
      assert t == 1
    };
    {
      var t: int := 2;
      assert t == 2
    }
  }
};

// A labeled block beside an unlabeled one, both declaring `t`: both are
// independently scoped, so the names do not collide.
procedure labeledAndUnlabeledSibling()
  entry
  opaque
{
  {
    var t: int := 3;
    assert t == 3
  } myLabel;
  {
    var t: int := 4;
    assert t == 4
  }
};
#end
