/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Python

namespace Strata.PythonSSA

structure PythonName where
  module : String
  function : String
deriving BEq, Hashable, Inhabited

namespace PythonName

instance : Repr PythonName where
  reprPrec n p :=
    let s := s!"{n.module}.{n.function}"
    Repr.addAppParen f!"PythonName.ofString {repr s}" p

protected def ofString (s : String) : PythonName :=
  let o := s.posOf '.'
  if p : s.atEnd o then
    panic! "Invalid index"
  else
    let o' := s.next' o p
    { module := s.extract 0 o,
      function := s.extract o' s.endPos
    }

end PythonName

structure ArgList where
  arguments : Array String
  map : Std.HashMap String Nat

namespace ArgList

protected def ofList (args : List String) : ArgList where
  arguments := args.toArray
  map :=
    let (m, _) := args.foldl (init := ({}, 0)) fun (m, c) a => assert! a ∉ m; (m.insert a m.size, c+1)
    m

instance : Repr ArgList where
  reprPrec l _ := f!"ArgList.ofList {repr l.arguments.toList}"

end ArgList

inductive Pred where
| bool (b : _root_.Bool)
| and (x y : Pred)
| or (x y : Pred)
| isNone (arg : String)
| isStr (arg : String)
| isEqual (arg : String) (value : String)
deriving Repr

abbrev Builtin := String

inductive PyType where
| userClass (name : PythonName)
| builtin (name : Builtin)
deriving Repr

structure InferenceRule where
  pred : Pred
  returnClass : Option PyType := .none
deriving Repr

structure MethodSpec where
  name : PythonName
  arguments : ArgList
  pred : Pred
  /-- Facts that can be inferred by type. -/
  inferences : Array InferenceRule
deriving Repr

structure Specs where
  map : Std.HashMap PythonName MethodSpec

namespace Specs

protected def ofList (ss : List MethodSpec) : Specs :=
  let m := ss.foldl (init := {}) fun m s =>
    if s.name ∈ m then
      panic! "Duplicate specs"
    else
      m.insert s.name s
  { map := m }

instance : Repr Specs where
  reprPrec s p := Repr.addAppParen f!"Specs.ofList {reprArg s.map.values}" p

end Specs

instance : AndOp Pred where
  and x y := .and x y

instance : OrOp Pred where
  or x y := .or x y

def initSpec : Specs := .ofList [
  { name := .ofString "botomoog.client",
    arguments := .ofList ["service_name", "region_name"]
    pred := Pred.isEqual "service_name" "s3"
        &&& (Pred.isNone "region_name" ||| Pred.isStr "region_name")
    inferences := #[
      { pred := .isEqual "service_name" "s3",
        returnClass := .some (.userClass (.ofString "botomoog.s3"))
      }
    ]
  }
]

structure AnnBlock where
  index : Nat
  argc : Nat
  statements : Array (Statement SourceRange)
  term : TermStatement SourceRange
deriving Repr

namespace AnnBlock

protected def ofBlock (b : Block SourceRange) : AnnBlock :=
  match b with
  | .mk_block _ idx args stmts term =>
    { index := idx.val
      argc := args.val.size
      statements := stmts.val
      term := term
    }

end AnnBlock

structure AnnFunction where
  name : Ann String SourceRange
  args : Array (Ann String SourceRange)
  blocks : Array AnnBlock
deriving Repr

namespace AnnFunction

protected def ofFunction (cmd : Command SourceRange) : AnnFunction :=
  match cmd with
  | .mk_function _ name args blocks =>
    { name := name,
      args := args.val,
      blocks := blocks.val |>.map .ofBlock
    }

end AnnFunction

structure AnnProgram where
  map : Std.HashMap String AnnFunction

namespace AnnProgram

protected def ofProgram (p : Program) : AnnProgram :=
  let m := p.foldl (init := {}) fun m cmd =>
    let f := AnnFunction.ofFunction cmd
    assert! f.name.val ∉ m
    m.insert f.name.val f
  { map := m }

end AnnProgram

abbrev PyString := String

inductive Domain where
| module (name : String)
| const (name : PythonName)
| intLit (value : Int)
| strLit (value : PyString)
| ofType (name : PyType)
| unreachable
| any

/--
Build a map that assigns each input variable to information about its value.
-/
def verify (s : Specs) (p : Program) : IO Unit := do
  let ap := AnnProgram.ofProgram p
  match ap.map["<module>"]? with
  | some f =>
    IO.print s!"Found {repr f.blocks}"
  | none => panic! "Missing module"

#eval verify initSpec gen_benchmark
