/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

namespace Core.Implicit

public section

/--
The heap effect of a procedure: whether it reads from, writes to, or
does not interact with the ambient heap.

- `.none` — the procedure does not touch the heap.
- `.reads` — the procedure reads from the heap but does not modify it.
- `.writes` — the procedure may modify the heap (implies reads).
-/
inductive HeapEffect where
  | none
  | reads
  | writes
  deriving Repr, DecidableEq, Inhabited, BEq

end

end Core.Implicit
