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

/-!
# CallGraph.computeRoots Tests

Tests for `CallGraph.computeRoots` which finds entry-point ("root") nodes
by iteratively removing sources and their reachable descendants, breaking
SCCs by choosing the alphabetically smallest member.
-/

-- Linear chain: a → b → c  ⟹  only "a" is a root
#guard linearGraph.computeRoots == ["a"]

-- Independent nodes (no edges between them)
private def independentGraph : CallGraph :=
  buildCallGraph [("a", []), ("b", []), ("c", [])]

#guard independentGraph.computeRoots == ["a", "b", "c"]

-- Mutual recursion: a ↔ b  ⟹  alphabetically smallest "a" is chosen
#guard mutualGraph.computeRoots == ["a"]

-- 3-node cycle: a → b → c → a  ⟹  "a" is chosen
#guard triangleGraph.computeRoots == ["a"]

-- Partial cycle: a → b ↔ c  ⟹  "a" is the only root (b,c reachable from a)
#guard partialCycleGraph.computeRoots == ["a"]

-- Root plus disjoint SCC: a → b, c ↔ d (c and d not reachable from a)
private def rootPlusSCC : CallGraph :=
  buildCallGraph [("a", ["b"]), ("b", []), ("c", ["d"]), ("d", ["c"])]

#guard rootPlusSCC.computeRoots == ["a", "c"]

-- Main calls helper, independent SCC not reachable from main
private def mainPlusSCC : CallGraph :=
  buildCallGraph [("__main__", ["helper"]), ("helper", []),
                   ("ping", ["pong"]), ("pong", ["ping"])]

#guard mainPlusSCC.computeRoots == ["__main__", "ping"]

-- computeRoots filtered to user procs (prelude never calls user code)
private def preludePlusUserGraph : CallGraph :=
  buildCallGraph [("prelude_init", ["prelude_helper"]), ("prelude_helper", []),
                   ("user_a", ["user_b"]), ("user_b", [])]

#guard preludePlusUserGraph.computeRoots.filter
    (["user_a", "user_b"].contains ·) == ["user_a"]

-- Empty graph
#guard CallGraph.empty.computeRoots == []

-- Single node, self-recursive
#guard selfRecursiveGraph.computeRoots == ["a"]

-- preferredRoots tie-breaker: SCC {a, b}, prefer ["b"] ⟹  "b" chosen over "a"
#guard mutualGraph.computeRoots (preferredRoots := ["b"]) == ["b"]

-- preferredRoots with multiple preferred in SCC: pick alphabetically smallest preferred
#guard triangleGraph.computeRoots (preferredRoots := ["c", "b"]) == ["b"]

-- preferredRoots when no preferred node is in the SCC: fall back to alphabetical
#guard mutualGraph.computeRoots (preferredRoots := ["z"]) == ["a"]

end Core.CallGraph.Tests
