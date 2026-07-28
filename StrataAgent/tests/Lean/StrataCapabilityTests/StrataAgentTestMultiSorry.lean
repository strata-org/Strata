

def fast_exponentiation (a: Nat) (n: Nat): Nat :=
  if n = 0 then 1
  else if n % 2 = 0 then
    let half := fast_exponentiation a (n / 2)
    half * half
  else
    a * fast_exponentiation a (n - 1)

def slow_exponentiation (a: Nat) (n: Nat): Nat :=
  if n = 0 then 1
  else a * slow_exponentiation a (n - 1)


theorem fast_exponentiation_lemma (a: Nat) (n: Nat):
  fast_exponentiation a n * fast_exponentiation a n = fast_exponentiation a (2 * n) :=
  by sorry


theorem fast_exponentiation_same_as_slow (a: Nat) (n: Nat):
  fast_exponentiation a n = slow_exponentiation a n := by sorry
