import Mathlib
/-!
# Examples for Lecture 2: Nilpotents in commutative rings
-/

/-- Example 1: If `a` is nilpotent, then `a * b` is nilpotent for any `b`. -/
lemma nilpotent_mul (R : Type) [CommRing R] (a b : R) (ha : IsNilpotent a) :
    IsNilpotent (a * b) := by
  rw [IsNilpotent] at *
  obtain ⟨n, hn⟩ := ha
  use n
  rw [mul_pow, hn, zero_mul]



/-- Helper lemma for example 2: If `I` is a prime ideal, and `a ^ n ∈ I` for some
`n`, then `a ∈ I`.
-/
lemma mem_primeIdeal_of_pow_mem (R : Type) [CommRing R]
    (I : Ideal R) (hI : Ideal.IsPrime I) (a : R) (n : ℕ) (ha : a ^ n ∈ I) :
    a ∈ I := by
  induction n with
  | zero => -- base case
      apply Ideal.mem_of_one_mem
      rw [pow_zero] at ha
      assumption
  | succ n ih => -- induction step
      rw [pow_succ] at ha
      have h : a ^ n ∈ I ∨ a ∈ I := by
        apply Ideal.IsPrime.mem_or_mem
        · assumption
        · assumption
      tauto


/-- Example 2: If `a` is nilpotent then `a` is in every prime ideal. -/
lemma mem_primeIdeal_of_nilpotent (R : Type) [CommRing R]
    (a : R) (ha : IsNilpotent a) (I : Ideal R) (hI : Ideal.IsPrime I) :
    a ∈ I := by
  rw [IsNilpotent] at ha
  obtain ⟨n, hn⟩ := ha
  apply mem_primeIdeal_of_pow_mem
  · assumption
  · rw [hn]
    apply Ideal.zero_mem



variable (R : Type) [CommRing R]

/-- Sums of nilpotents are nilpotent. -/
lemma IsNilpotent.add (a b : R) (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use m + n -- show (a + b) ^ (m + n) = 0
  rw [add_pow] -- the binomial theorem
  apply Finset.sum_eq_zero -- "a sum is zero if all its terms are zero"
  intro i hi
  by_cases hm' : m ≤ i
  · have : i = m + (i - m) := by omega
    rw [this, pow_add, hm, zero_mul, zero_mul, zero_mul]
  · have : m + n - i = n + (m - i) := by omega
    simp [this, pow_add, hn]


/-- The nilradical of an ideal. [Duplicates an existing definition in mathlib]. -/
def my_nilradical : Ideal R where
  carrier := {a : R | IsNilpotent a}
  zero_mem' := by simp
  add_mem' := by apply IsNilpotent.add
  smul_mem' s t := by
    rintro ⟨n, hn⟩
    use n
    rw [smul_eq_mul, mul_pow, hn, mul_zero]
