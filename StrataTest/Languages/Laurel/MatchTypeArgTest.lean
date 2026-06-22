/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataDDM.Util.IO
meta import Strata.Languages.Laurel.MonomorphizeComposites
meta section
open Strata.Laurel
namespace Strata.Laurel.MatchTypeArgTest
-- HighType builders
def hi (h : HighType) : HighTypeMd := ⟨h, none⟩
def tv (s : String) : HighType := .TVar (mkId s)
def ud (s : String) : HighType := .UserDefined (mkId s)
def app (base : HighType) (args : List HighType) : HighType := .Applied (hi base) (args.map hi)
-- lookup helper
def look (m : Option (Std.HashMap String HighType)) (k : String) : Option HighType :=
  m.bind (·.get? k)

def run : IO Unit := do
  let e : Std.HashMap String HighType := {}
  -- (1) Box<T> vs Box<int> → T = int
  let r1 := matchTypeArg (app (ud "Box") [tv "T"]) (app (ud "Box") [.TInt]) e
  unless (look r1 "T" |>.isSome) do throw (IO.userError "case1: T not bound")
  match look r1 "T" with | some .TInt => pure () | _ => throw (IO.userError "case1: T should be int")
  -- (2) nested Box<Box<T>> vs Box<Box<bool>> → T = bool
  let r2 := matchTypeArg (app (ud "Box") [app (ud "Box") [tv "T"]]) (app (ud "Box") [app (ud "Box") [.TBool]]) e
  match look r2 "T" with | some .TBool => pure () | _ => throw (IO.userError "case2: nested T should be bool")
  -- (3) two params, T consistent (Pair<T,T> vs Pair<int,int>) → ok
  let r3 := matchTypeArg (app (ud "Pair") [tv "T", tv "T"]) (app (ud "Pair") [.TInt, .TInt]) e
  unless r3.isSome do throw (IO.userError "case3: consistent T should succeed")
  -- (4) two params, T INCONSISTENT (Pair<T,T> vs Pair<int,bool>) → none
  let r4 := matchTypeArg (app (ud "Pair") [tv "T", tv "T"]) (app (ud "Pair") [.TInt, .TBool]) e
  unless r4.isNone do throw (IO.userError "case4: inconsistent T must FAIL (none)")
  -- (5) arity mismatch (Box<T> vs Box<int,bool>) → none
  let r5 := matchTypeArg (app (ud "Box") [tv "T"]) (app (ud "Box") [.TInt, .TBool]) e
  unless r5.isNone do throw (IO.userError "case5: arity mismatch must FAIL (none)")
  -- (6) bare T vs concrete composite → T = that composite
  let r6 := matchTypeArg (tv "T") (ud "Widget") e
  match look r6 "T" with | some (.UserDefined n) => unless n.text == "Widget" do throw (IO.userError "case6 name") | _ => throw (IO.userError "case6: T should be Widget")
  -- (7) DIFFERENT base names, same arity (Box<T> vs Pair<int>) → none (item-10C self-guard).
  --     Before the guard this bound T=int on arity alone (the heads are both UserDefined and the
  --     head recursion binds nothing); now monomorphization is self-guarding on the base name.
  let r7 := matchTypeArg (app (ud "Box") [tv "T"]) (app (ud "Pair") [.TInt]) e
  unless r7.isNone do throw (IO.userError "case7: different base names must FAIL (none)")
  IO.println "matchTypeArg: all 7 cases OK"

#guard_msgs (drop info, error) in
#eval run
end Strata.Laurel.MatchTypeArgTest
