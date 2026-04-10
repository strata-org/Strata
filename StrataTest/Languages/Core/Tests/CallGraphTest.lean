/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CallGraph

/-!
# CallGraph.isRecursive Tests

Tests for `CallGraph.isRecursive` which detects whether a procedure is part
of a cycle (SCC) in the call graph.
-/

namespace Core.CallGraph.Tests

open Core

-- a → b → c (linear chain, no cycles)
private def linearGraph : CallGraph :=
  buildCallGraph [("a", ["b"]), ("b", ["c"]), ("c", [])]

#guard !linearGraph.isRecursive "a"
#guard !linearGraph.isRecursive "b"
#guard !linearGraph.isRecursive "c"

-- a → a (direct self-recursion)
private def selfRecursiveGraph : CallGraph :=
  buildCallGraph [("a", ["a"])]

#guard selfRecursiveGraph.isRecursive "a"

-- a → b → a (mutual recursion)
private def mutualGraph : CallGraph :=
  buildCallGraph [("a", ["b"]), ("b", ["a"])]

#guard mutualGraph.isRecursive "a"
#guard mutualGraph.isRecursive "b"

-- a → b → c → a (3-node cycle)
private def triangleGraph : CallGraph :=
  buildCallGraph [("a", ["b"]), ("b", ["c"]), ("c", ["a"])]

#guard triangleGraph.isRecursive "a"
#guard triangleGraph.isRecursive "b"
#guard triangleGraph.isRecursive "c"

-- a → b → c → b (b and c form a cycle, a does not)
private def partialCycleGraph : CallGraph :=
  buildCallGraph [("a", ["b"]), ("b", ["c"]), ("c", ["b"])]

#guard !partialCycleGraph.isRecursive "a"
#guard partialCycleGraph.isRecursive "b"
#guard partialCycleGraph.isRecursive "c"

-- Disconnected: a → b, c → c (only c is recursive)
private def disconnectedGraph : CallGraph :=
  buildCallGraph [("a", ["b"]), ("b", []), ("c", ["c"])]

#guard !disconnectedGraph.isRecursive "a"
#guard !disconnectedGraph.isRecursive "b"
#guard disconnectedGraph.isRecursive "c"

-- Unknown node not in graph
#guard !linearGraph.isRecursive "unknown"

-- Empty graph
private def emptyGraph : CallGraph := buildCallGraph []

#guard !emptyGraph.isRecursive "anything"

end Core.CallGraph.Tests
