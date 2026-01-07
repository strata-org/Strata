/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
namespace Strata.Deser

abbrev Error := String

/--
A `BufferM` monad has access to a byte array and returns either a value of type `α` or an error.
-/
@[expose] def BufferM (α : Type) := ReaderT ByteArray (Except (Nat × Error)) α

namespace BufferM

instance {α} : Inhabited (BufferM α) where
  default := private fun _ => .error (0, "")

@[instance]
def instMonad : Monad BufferM := inferInstanceAs (Monad (ReaderT _ _))

protected def contents : BufferM ByteArray := Except.ok

protected def fail (off : Nat) (msg : String) : BufferM α := fun _ => .error (off, msg)

end BufferM

/--
This tracks the remaining number of bytes in the reader left.
-/
@[expose] def Fuel := Nat

namespace Fuel

def toNat (f : Fuel) : Nat := f

instance : LE Fuel := inferInstanceAs (LE Nat)

@[instance]
def instDecidableLe (x y : Fuel) : Decidable (x ≤ y) := inferInstanceAs (Decidable (x.toNat ≤ y.toNat))

instance : LT Fuel := inferInstanceAs (LT Nat)

@[instance]
def instDecidableLt (x y : Fuel) : Decidable (x < y) := inferInstanceAs (Decidable (x.toNat < y.toNat))

def le_refl (f : Fuel) : f ≤ f := f.toNat.le_refl

instance {x} : OfNat Fuel x where
  ofNat := x

instance instSubFuelNat : HSub Fuel Nat Fuel where
  hSub x y := x.toNat - y

instance instSubNatFuel : HSub Nat Fuel Nat where
  hSub x y := x - y.toNat

def sub_le (f : Fuel) (n : Nat) : f - n ≤ f := Nat.sub_le f n

end Fuel

/-- Flag indicating whether the Reader monad has consumed file. -/
inductive Progress where
/-- Reader must consume at least one byte. -/
| strict
/-- Reader may consume zero bytes -/
| any

namespace Progress

/-- `Satisfies m f g` holds if the transitioning from fuel `f` to `g` satisfies the progress constraint. -/
@[simp]
def Satisfies : Fuel × Fuel → Progress → Prop
| (n, m), .strict => m < n
| (n, m), .any => m ≤ n

infix:45  " ⊧ " => Progress.Satisfies

/-- Return the strongest condition of two progress values. -/
@[simp, expose]
def meet : Progress → Progress → Progress
| strict, _ => strict
| any, x => x

/-- This shows that we -/
theorem meet_trans {m n : Progress} : Satisfies (a, b) m → Satisfies (b, c) n → Satisfies (a, c) (meet m n) := by
  cases m <;> cases n <;> (simp [Fuel] ; omega)

end Progress

namespace Fuel

/-- Preimage of elements less than fuel value with respect to progress constraint -/
@[expose] def Pre (f : Fuel) (m : Progress) : Type := { x : Fuel // (f, x) ⊧ m }

/-- Unchanged value of fuel with any constraint. -/
def unchanged (f : Fuel) : f.Pre .any := ⟨f, f.le_refl⟩

end Fuel

protected def BufferM.curOffset (fuel : Fuel) : BufferM Nat := return (←.contents).size - fuel

/- Reader is a buffer with a fuel argument for tracking progress. -/
@[expose] def Reader (m : Progress) α := ∀(f : Fuel), BufferM (α × f.Pre m)

/- Reader with strict progress -/
abbrev SReader := Reader .strict

/- Reader with any progress -/
abbrev AReader := Reader .any

protected def BufferM.ofReader {m α} (fuel : Fuel) (act : Reader m α) : BufferM (α × fuel.Pre m) :=
  act fuel

namespace Reader

protected def pure {α} (a : α) : Reader .any α := fun f => pure (a, f.unchanged)

protected def map {α β m} (f : α → β) (h : Reader m α) : Reader m β := fun fuel =>
  (fun (a, f1) => (f a, f1)) <$> h fuel

protected def bind {m α n β} (g : Reader m α) (h : α → Reader n β) : Reader (.meet m n) β := fun f => do
  let (a, ⟨f1, f1p⟩) ← g f
  let (b, ⟨f2, f2p⟩) ← h a f1
  .pure (b, ⟨f2, Progress.meet_trans f1p f2p⟩)

/--
Specialized bind that reads a strict reader first so any reader may follow.

Used to ensure progress values do not need to be inferred.
-/
protected def bindAny {α β} (g : SReader α) (h : α → AReader β) : SReader β := .bind g h

instance {m} : Functor (Reader m) where
  map := .map

instance : Monad AReader where
  pure := .pure
  bind := .bind

instance : Bind SReader where
  bind := .bind

protected def fail {m α} (off : Nat) (msg : String) : Reader m α := fun _ => .fail off msg

protected def ofLT (act : SReader α) : AReader α := fun f =>
  (fun (a, ⟨f2, p⟩) => (a, ⟨f2, Nat.le_of_lt p⟩)) <$> act f

protected def ofM (act : ∀(fuel : Fuel), BufferM (α × fuel.Pre m)) : Reader m α := act

@[inline]
protected def peekM (act : Nat → BufferM α) : AReader α := fun f => do
  return (← act f, f.unchanged)

@[inline]
protected def peekM' (act : BufferM α) : AReader α := fun f => do
  return (← act, f.unchanged)

instance : MonadReader ByteArray AReader where
  read := private .peekM' .contents

protected def curOffset : AReader Nat :=
  .peekM fun f => return (← .contents).size - f

def canRead (len : Nat) : AReader Bool :=
  .peekM fun f => .pure (f >= len)

protected def skip! (len : Nat) : AReader Unit := fun f => do
  .pure ((), ⟨f - len, Fuel.sub_le f len⟩)

protected def skip (off : Nat) (len : Nat) : AReader Unit := fun f => do
  if f ≥ len then
    .pure ((), ⟨f - len, Fuel.sub_le f len⟩)
  else
    .fail off s!"Skipped past end of file."

def readByte : Reader m UInt8 := fun f => do
  let bs ← .contents
  if p : f > 0 then
    assert! bs.size ≥ f
    .pure (bs[bs.size - f]!, .mk (f - 1) (by cases m <;> simp [Fuel] at *; omega))
  else
    .fail bs.size "Read past end of file."

def readBuffer (len : Nat) : AReader ByteArray := fun f => do
  let contents ← .contents
  let off := contents.size - f
  if f ≥ len then
    .pure (contents.extract off (off + len), .mk _ (Fuel.sub_le f len))
  else
    .fail off s!"Read past end of file."

end Reader

/- readUpTo/readSeqUpto -/

inductive Step (α : Type u) (β : Type v) where
  | done  : β → Step α β
  | yield : α → Step α β
deriving Inhabited

@[simp] theorem Fuel.sub_toNat (f : Fuel) (n : Nat) : (f - n).toNat = f.toNat - n := by rfl

namespace BufferM

private def readUpto.aux {α} (init : Fuel) (act : ∀(fuel : init.Pre .any), α → BufferM (α × fuel.val.Pre .strict)) (v : α) (fuel : init.Pre .any) (limit : Nat) : BufferM (α × init.Pre .any) := do
  if (← .curOffset fuel.val) < limit then
    let (v, ⟨fuel2, p⟩) ← act fuel v
    have q : fuel2 < init := Progress.meet_trans fuel.property p
    readUpto.aux init act v ⟨fuel2, Nat.le_of_lt q⟩ limit
  else
    pure (v, fuel)
termination_by fuel.val.toNat

def readUpto {α} (fuel : Fuel) (init : α) (limit : Nat) (act : ∀(fuel : fuel.Pre .any), α → BufferM (α × fuel.val.Pre .strict)) : BufferM (α × fuel.Pre .any) := do
  readUpto.aux fuel act init fuel.unchanged limit

def readSeqUpto {α} (fuel : Fuel) (limit : Nat) (act : ∀(fuel : fuel.Pre .any), BufferM (α × fuel.val.Pre .strict)) : BufferM (Array α × fuel.Pre .any) := do
  readUpto fuel #[] limit fun fuel a => (fun (v, p) => (a.push v, p)) <$> act fuel

def readWhile {α β} (fuel : Fuel) (init : α) (act : α → UInt8 → Step α β) : BufferM (β × fuel.Pre .strict) := aux fuel.unchanged init
  where aux (f : fuel.Pre .any) (v : α) : BufferM (β × fuel.Pre .strict) := do
    let contents ← .contents
    let o := contents.size - f.val.toNat
    if p : f.val.toNat > 0 then
      let b := contents[o]!
      match act v b with
      | .yield v =>
        let f2 : fuel.Pre .any := ⟨f.val - 1, Progress.meet_trans f.property (Nat.sub_le f.val.toNat 1) ⟩
        aux f2 v
      | .done v =>
        let f2 : fuel.Pre .strict := ⟨f.val - 1, Progress.meet_trans f.property (Nat.sub_lt p Nat.zero_lt_one) ⟩
        pure (v, f2)
    else
      .fail o s!"Unexpected end of file"
    termination_by f.val.toNat

end BufferM

namespace Reader

def readUpto {α} (init : α) (limit : Nat) (act : α → SReader α) : AReader α :=
  .ofM fun fuel => .readUpto fuel init limit (fun fuel a => .ofReader fuel.val (act a))

def readSeqUpto {α} (limit : Nat) (act : SReader α) : AReader (Array α) :=
  .ofM fun fuel => .readSeqUpto fuel limit (.ofReader ·.val act)

def readWhile {α β} (init : α) (act : α → UInt8 → Step α β) : SReader β :=
  .ofM fun fuel => .readWhile fuel init act

end Strata.Deser.Reader
end
