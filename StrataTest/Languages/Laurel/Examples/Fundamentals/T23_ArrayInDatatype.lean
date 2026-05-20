/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

-- `Array<T>` cannot be used as a datatype constructor argument: the
-- combination doesn't typecheck (datatypes carry value semantics, but
-- `Array<T>` is a heap reference). The validator catches this with a
-- dedicated diagnostic so the user sees a clear explanation rather than
-- an opaque Core type-checker unification error.
--
-- Workarounds: use a `composite` instead of a `datatype`, or wrap a
-- `Seq<T>` snapshot.

def arrayInDatatypeProgram := r"
datatype Wrapped {
  Wrap(arr: Array<int>)
//          ^^^^^^^^^^ error: not supported as a datatype constructor argument
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArrayInDatatype" arrayInDatatypeProgram 14 processLaurelFile

-- A `Seq<int>` constructor argument is fine — sequences have value
-- semantics. This positive test pins the contrast to the negative case
-- above.

def seqInDatatypeProgram := r"
datatype WrappedSeq {
  WrapSeq(items: Seq<int>)
}

procedure constructAndCompare()
  opaque
{
  var s1: Seq<int> := [1, 2, 3];
  var s2: Seq<int> := [1, 2, 3];
  var w1: WrappedSeq := WrapSeq(s1);
  var w2: WrappedSeq := WrapSeq(s2);
  assert w1 == w2
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "SeqInDatatype" seqInDatatypeProgram 14 processLaurelFile

end Laurel
end Strata
