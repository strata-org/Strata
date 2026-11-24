/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.MonomorphizeFunctions
meta import Strata.DL.SMT.Symbol
meta import Strata.Languages.Core.NameManglingProps

meta section

open Strata

/-! # The prefix of monomorphization's copies

A copy's name is `P#<escaped base>#<types>` (`Core.NameMangling.mangleFuncName`). `P` is
`$__mono` unless a name of the program or the factory starts with `$__mono`; then it is padded
with `_` so that no such name starts with `P#` (`choosePrefix_fresh`). These tests pin which
names make it pad, including variables and binders, which the SMT encoder declares in the same
namespace as functions, and that no program is rejected for its names. -/

namespace Core.MonomorphizeFunctions.CopyPrefixTests

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

/-- Type-check `t`, run monomorphization, and return the prefix it chose and the names of
    the program's functions afterwards. -/
private def monoPrefixAndFns (t : StrataDDM.Program) : Except String (String × List String) := do
  let tc ← (Core.typeCheck quietOpts (translate t)).mapError (fun e => toString (e.format none))
  let seed := { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
  let (res, _) := Core.Transform.runWith tc Core.MonomorphizeFunctions.run seed
  match res with
  | .ok p => return ((Core.MonomorphizeFunctions.collectPolymorphicFuncDecls tc Core.Factory).copyPrefix,
      p.decls.filterMap fun
      | .func f _ => some f.name.name
      | _ => none)
  | .error e => throw (toString (e.format none))

private def plainPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(out r : int)
spec { ensures r == 5; }
{ r := id(5); };
#end

-- Without a name starting with `$__mono`, the prefix is the plain one, and the copy's name is
-- the one the base pipeline gives it.
#guard monoPrefixAndFns plainPgm matches .ok ("$__mono", ["$__mono#id#int"])

/-- A factory function whose parameter is named like the copy of `id` at `int`. The encoder
    declares a factory function's parameters by name, and monomorphization may rewrite its body
    to call copies, so the parameter pads the prefix. -/
private def paramLike : Lambda.LFunc Core.CoreLParams :=
  { name := ⟨"g", ()⟩, inputs := [(⟨"$__mono#id#int", ()⟩, .int)], output := .int }

#guard match Core.typeCheck quietOpts (translate plainPgm) with
  | .ok tc =>
    let pfx := (Core.MonomorphizeFunctions.collectPolymorphicFuncDecls tc
      (Core.Factory.pushIfNew paramLike)).copyPrefix
    pfx.startsWith "$__mono_" && !"$__mono#id#int".startsWith (pfx ++ "#")
  | .error _ => false

/-- A function named exactly like the copy the plain prefix would make. -/
private def fnClashPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
function |$__mono#id#int|(x : int) : int { int.add(x, 1) }
procedure P(out r : int)
spec { ensures r == 5; }
{ r := id(5); };
#end

-- Not rejected: the prefix is padded, and the user's function keeps its name.
#guard match monoPrefixAndFns fnClashPgm with
  | .ok (pfx, fns) => pfx != "$__mono" && fns.contains "$__mono#id#int" &&
      fns.contains (pfx ++ "#id#int")
  | .error _ => false

/-- A variable named exactly like the copy the plain prefix would make. -/
private def varClashPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(|$__mono#id#int| : int, out r : int)
spec { ensures r == |$__mono#id#int|; }
{ r := id(|$__mono#id#int|); };
#end

-- The prefix is padded with `_`, and the copy of `id` takes the padded name, apart from the
-- parameter named `$__mono#id#int`.
#guard match monoPrefixAndFns varClashPgm with
  | .ok (pfx, fns) => pfx.startsWith "$__mono_" && fns.contains (pfx ++ "#id#int") &&
      !fns.contains "$__mono#id#int"
  | .error _ => false

/-- A bound variable named exactly like the copy the plain prefix would make. -/
private def binderClashPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
axiom [ax]: forall |$__mono#id#int| : int :: id(|$__mono#id#int|) == |$__mono#id#int|;
#end

-- The prefix is padded with `_`, and the copy of `id` takes the padded name, apart from the
-- bound variable named `$__mono#id#int`.
#guard match monoPrefixAndFns binderClashPgm with
  | .ok (pfx, fns) => pfx.startsWith "$__mono_" && fns.contains (pfx ++ "#id#int") &&
      !fns.contains "$__mono#id#int"
  | .error _ => false

/-- An axiom named exactly like the copy the plain prefix would make. Declaration names share one
    namespace, so the copy, a function declaration, must not take it. -/
private def axiomClashPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
axiom [|$__mono#id#int|]: id(3) == 3;
procedure P(out r : int)
spec { ensures [rIs5]: r == 5; }
{ r := id(5); };
#end

-- The prefix is padded, and the program verifies with the user's meaning.
#guard match monoPrefixAndFns axiomClashPgm with
  | .ok (pfx, fns) => pfx != "$__mono" && fns.contains (pfx ++ "#id#int")
  | .error _ => false

#guard_msgs (drop info) in
#eval do
  let rs ← Strata.Core.verify axiomClashPgm
  let v := rs.toList.map fun (r : _root_.Core.VCResult) => (r.obligation.label, r.isSuccess)
  unless v == [("rIs5", true)] do throw (IO.userError s!"axiomClashPgm: {v}")

/-! ## Type names that look like an arity, a width or the bitvector tag

A type constructor named all digits or exactly `$bv` is marked `?n` in a copy's name
(`needsMark`), so it cannot be read as an arity, a width or `$bv` (`mangleTyArgs_inj`). -/

private def numTyPgm :=
#strata
program Core;
type |123|;
type |$bv|;
function id<a>(x : a) : a { x }
procedure P(t : |123|, u : |$bv|, out r : |123|, out s : |$bv|)
spec { ensures r == t; ensures s == u; }
{ r := id(t); s := id(u); };
#end

#guard monoPrefixAndFns numTyPgm matches .ok ("$__mono", ["$__mono#id#?n123", "$__mono#id#?n$bv"])

-- The two copies differ from each other and from a bitvector instance's name.
#guard NameMangling.mangleTyArgs [.tcons "123" []] != NameMangling.mangleTyArgs [.bitvec 123]
#guard NameMangling.mangleTyArgs [.tcons "$bv" []] != NameMangling.mangleTyArgs [.bitvec 0]

/-- A datatype's type parameter named exactly like the copy the plain prefix would make. The SMT
    encoder binds a datatype's parameters by name, so the copies' prefix must avoid it. -/
private def dtParamClashPgm :=
#strata
program Core;
datatype Box (|$__mono#id#int| : Type) { MkBox(v : |$__mono#id#int|) };
function id<a>(x : a) : a { x }
procedure P(b : Box int, out r : int)
spec { ensures [rIsV]: r == Box..v(b); }
{ r := id(Box..v(b)); };
#end

-- The prefix is padded, and the program verifies with the user's meaning.
#guard match monoPrefixAndFns dtParamClashPgm with
  | .ok (pfx, fns) => pfx.startsWith "$__mono_" && fns.contains (pfx ++ "#id#int") &&
      !fns.contains "$__mono#id#int"
  | .error _ => false

#guard_msgs (drop info) in
#eval do
  let rs ← Strata.Core.verify dtParamClashPgm
  let v := rs.toList.map fun (r : _root_.Core.VCResult) => (r.obligation.label, r.isSuccess)
  unless v == [("rIsV", true)] do throw (IO.userError s!"dtParamClashPgm: {v}")

/-! ## Escaped names -/

/-- A polymorphic function and a type whose names contain `#` and `?`. -/
private def escPgm :=
#strata
program Core;
type |T#1|;
function |f?#|<a>(x : a) : a { x }
procedure P(t : |T#1|, out r : |T#1|)
spec { ensures r == t; }
{ r := |f?#|(t); };
#end

-- The copy's name escapes `?` as `??` and `#` as `?h`, so it has exactly two `#`.
#guard monoPrefixAndFns escPgm matches .ok ("$__mono", ["$__mono#f???h#T?h1"])

-- The display name is the user's (`demangleFuncName` decodes the base).
#guard NameMangling.demangleFuncName NameMangling.monoPrefix "$__mono#f???h#T?h1" == some ("f?#", "T?h1")

-- The SMT printer writes `?` as itself, except first.
#guard Strata.SMT.Symbol.escapeForSMT "$__mono#f???h#T?h1" == "$__mono#f???h#T?h1"

/-! ## The padded prefix end to end

A user function named exactly like the copy the plain prefix would make, used next to that copy,
and a map built by `update` (a collection operator whose copy the SMT encoder looks up by the
prefix). Each `ensures` holds only if the copy and the user's function stay apart, and the
results name the user's function as written. -/

private def paddedVerifyPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
function |$__mono#id#int|(x : int) : int { int.add(x, 1) }
procedure P(out r : int, out s : int, out m : Map int int)
spec {
  ensures [copyIsId]: r == 5;
  ensures [userFnKept]: s == 6;
  ensures [mapUpdated]: m[1] == 2;
}
{
  r := id(5);
  s := |$__mono#id#int|(5);
  m := m[1 := 2];
};
#end

-- The verdicts; the printed obligations are pinned below.
#guard_msgs (drop info) in
#eval do
  let rs ← Strata.Core.verify paddedVerifyPgm
  let v := rs.toList.map fun (r : _root_.Core.VCResult) => (r.obligation.label, r.isSuccess)
  unless v == [("copyIsId", true), ("userFnKept", true), ("mapUpdated", true)] do
    throw (IO.userError s!"paddedVerifyPgm: {v}")

-- The verbose obligation dump decodes copies under any prefix monomorphization can choose, so
-- the padded copies show as `id(5)` and `m@1[1:=2]`. **Known display limitation, pinned:** the
-- printer does not know the chosen prefix, so the user's `$__mono#id#int` also shows as `id` in
-- `userFnKept`'s obligation. The verdicts are right.
/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: copyIsId
Property: assert
Obligation:
id(5) == 5

Label: userFnKept
Property: assert
Obligation:
id(5) == 6

Label: mapUpdated
Property: assert
Obligation:
(m@1[1:=2])[1] == 2

---
info:
Obligation: copyIsId
Property: assert
Result: ✅ pass

Obligation: userFnKept
Property: assert
Result: ✅ pass

Obligation: mapUpdated
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify paddedVerifyPgm

end Core.MonomorphizeFunctions.CopyPrefixTests

end
