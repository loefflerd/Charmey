import Mathlib

variable {R : Type*} [Ring R]

/-- If `I` is a prime ideal, and `a ^ n ∈ I` for some `n`, then `a ∈ I`. -/
lemma mem_primeIdeal_of_pow_mem
    {I : Ideal R} (hI : Ideal.IsPrime I) {a : R} {n : ℕ} (ha : a ^ n ∈ I) :
    a ∈ I := by
  induction n with
  | zero => -- base case
      rw [pow_zero] at ha
      rw [← mul_one a]
      apply Ideal.mul_mem_left
      assumption
  | succ n ih => -- induction step
      rw [pow_succ] at ha
      have ha' : a ^ n ∈ I ∨ a ∈ I := by
        apply Ideal.IsPrime.mem_or_mem
        · assumption
        · assumption
      rcases ha' with h | h
      · apply ih
        assumption
      · assumption


/-- If `a` is nilpotent then `a` is in every prime ideal. -/
lemma mem_primeIdeal_of_nilpotent
    {a : R} (ha : IsNilpotent a) {I : Ideal R} (hI : Ideal.IsPrime I) :
    a ∈ I := by
  rw [IsNilpotent] at ha
  obtain ⟨n, hn⟩ := ha
  apply mem_primeIdeal_of_pow_mem
  · assumption
  · rw [hn]
    apply Ideal.zero_mem

/-- If `I` is a prime ideal, and `a ^ n ∈ I` for some `n`, then `a ∈ I`. -/
lemma mem_primeIdeal_of_pow_mem'
    {I : Ideal R} (hI : I.IsPrime) {a : R} {n : ℕ} (ha : a ^ n ∈ I) :
    a ∈ I := by
  induction n with
  | zero => exact mul_one a ▸ I.mul_mem_left a (pow_zero a ▸ ha)
  | succ n ih => exact (hI.mem_or_mem (pow_succ a n ▸ ha)).elim ih id

omit [Ring R]

variable [CommRing R]

lemma IsNilpotent.add {a b : R} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use m + n
  rw [add_pow]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hm' : m ≤ i
  · have : i = m + (i - m) := by omega
    rw [this, pow_add, hm, zero_mul, zero_mul, zero_mul]
  · have : m + n - i = n + (m - i) := by omega
    simp [this, pow_add, hn]

variable {S : Type*} [CommRing S]

def nilRadical : Submodule S S :=
{ carrier := {a : S | IsNilpotent a}
  zero_mem' := by simp
  add_mem' := IsNilpotent.add
  smul_mem' s t := by
    rintro ⟨n, hn⟩
    use n
    rw [smul_eq_mul, mul_pow, hn, mul_zero] }
