module
public import Std.Data.HashSet

public section
namespace Strata.DDM

/--
This is a hashset backed by an array so that we can fold
over the elements in the set.
-/
structure OrderedSet (α : Type _) [BEq α] [Hashable α] where
  private mk ::
  private set : Std.HashSet α := {}
  private values : Array α := #[]

namespace OrderedSet

/-- empty set. -/
@[inline]
def empty {α} [BEq α] [Hashable α] : OrderedSet α := .mk {} #[]

/--
Return
-/
def toArray {α} [BEq α] [Hashable α] (s : OrderedSet α) : Array α := s.values

/-- Add an element to the set -/
def insert {α} [BEq α] [Hashable α] (s : OrderedSet α) (a : α) : OrderedSet α :=
  if a ∈ s.set then
    s
  else
    { set := s.set.insert a, values := s.values.push a }

/--
Add all reachable dialects
-/
partial def addAllPostorder {α} [BEq α] [Hashable α] (pre : α → Array α) (s : OrderedSet α) (a : α) : OrderedSet α :=
  if a ∈ s.set then
    s
  else
    let as := pre a
    let s := { s with set := s.set.insert a }
    let s := as.foldl (init := s) (addAllPostorder pre)
    { s with values := s.values.push a }

end OrderedSet

end Strata.DDM
end
