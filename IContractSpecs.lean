/-
  Hardcoded icontract specs for bisect and heapq modules.
  Smoke test: constructs Signature values and writes them as .pyspec.st.ion files.

  Usage: lake exe icontractSpecs <output_dir>
  Produces: <output_dir>/bisect.pyspec.st.ion
            <output_dir>/heapq.pyspec.st.ion
-/
import Strata.Languages.Python.Specs.DDM

open Strata.Python.Specs
open Strata.Python

namespace IContractSpecs

-- Helper: SpecType for List[int]
private def listIntType : SpecType :=
  .ident .none .typingList #[.ident .none .builtinsInt]

-- Helper: SpecType for int
private def intType : SpecType := .ident .none .builtinsInt

-- Helper: SpecType for None
private def noneType : SpecType := .ofAtom .none .noneType

/-! ## bisect module specs -/

/-- bisect_left(a, x, lo=0, hi=None)
    Preconditions from icontract:
      - isinstance(a, list)
      - isinstance(x, int)
    (a == sorted(a) is too complex → placeholder) -/
def bisectLeft : Signature := .functionDecl {
  loc := .none
  nameLoc := .none
  name := "bisect_left"
  args := {
    args := #[
      { name := "a", type := listIntType },
      { name := "x", type := intType },
      { name := "lo", type := intType, default := some .none },
      { name := "hi", type := intType, default := some .none }
    ]
    kwonly := #[]
  }
  returnType := intType
  isOverload := false
  preconditions := #[
    { message := #[.str "isinstance(a, list)"],
      formula := .isInstanceOf (.var "a" .none) "list" .none },
    { message := #[.str "a == sorted(a)"],
      formula := .placeholder .none },
    { message := #[.str "isinstance(x, int)"],
      formula := .isInstanceOf (.var "x" .none) "int" .none }
  ]
  postconditions := #[]
}

/-- insort_left(a, x, lo=0, hi=None)
    Same preconditions as bisect_left -/
def insortLeft : Signature := .functionDecl {
  loc := .none
  nameLoc := .none
  name := "insort_left"
  args := {
    args := #[
      { name := "a", type := listIntType },
      { name := "x", type := intType },
      { name := "lo", type := intType, default := some .none },
      { name := "hi", type := intType, default := some .none }
    ]
    kwonly := #[]
  }
  returnType := noneType
  isOverload := false
  preconditions := #[
    { message := #[.str "isinstance(a, list)"],
      formula := .isInstanceOf (.var "a" .none) "list" .none },
    { message := #[.str "a == sorted(a)"],
      formula := .placeholder .none },
    { message := #[.str "isinstance(x, int)"],
      formula := .isInstanceOf (.var "x" .none) "int" .none }
  ]
  postconditions := #[]
}

def bisectSignatures : Array Signature := #[bisectLeft, insortLeft]

/-! ## heapq module specs -/

/-- heappush(heap, item)
    Precondition: isinstance(heap, list) -/
def heappush : Signature := .functionDecl {
  loc := .none
  nameLoc := .none
  name := "heappush"
  args := {
    args := #[
      { name := "heap", type := listIntType },
      { name := "item", type := intType }
    ]
    kwonly := #[]
  }
  returnType := noneType
  isOverload := false
  preconditions := #[
    { message := #[.str "isinstance(heap, list)"],
      formula := .isInstanceOf (.var "heap" .none) "list" .none }
  ]
  postconditions := #[]
}

/-- heappop(heap)
    Preconditions:
      - isinstance(heap, list)
      - len(heap) >= 1 -/
def heappop : Signature := .functionDecl {
  loc := .none
  nameLoc := .none
  name := "heappop"
  args := {
    args := #[
      { name := "heap", type := listIntType }
    ]
    kwonly := #[]
  }
  returnType := intType
  isOverload := false
  preconditions := #[
    { message := #[.str "isinstance(heap, list)"],
      formula := .isInstanceOf (.var "heap" .none) "list" .none },
    { message := #[.str "len(heap) >= 1"],
      formula := .intGe (.len (.var "heap" .none) .none) (.intLit 1 .none) .none }
  ]
  postconditions := #[]
}

def heapqSignatures : Array Signature := #[heappush, heappop]

end IContractSpecs

def main (args : List String) : IO Unit := do
  let outDir ← match args.head? with
    | some d => pure d
    | none => do
      IO.eprintln "Usage: icontractSpecs <output_dir>"
      IO.Process.exit 1
  IO.FS.createDirAll outDir
  let bisectPath : System.FilePath := outDir / "bisect.pyspec.st.ion"
  let heapqPath : System.FilePath := outDir / "heapq.pyspec.st.ion"
  Strata.Python.Specs.writeDDM bisectPath IContractSpecs.bisectSignatures
  IO.println s!"Wrote {bisectPath} ({IContractSpecs.bisectSignatures.size} signatures)"
  Strata.Python.Specs.writeDDM heapqPath IContractSpecs.heapqSignatures
  IO.println s!"Wrote {heapqPath} ({IContractSpecs.heapqSignatures.size} signatures)"
