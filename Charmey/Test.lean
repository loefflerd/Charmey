import Mathlib

/-- If an element of a monoid has a right inverse, and a left inverse, then they are equal. -/
theorem Example1 {M : Type*} [Monoid M] (a b c : M) (h1 : a * b = 1) (h2 : c * a = 1) :
    b = c := by
  rw [← one_mul b] -- "one_mul b" is a proof that `1 * b = b`
  rw [← h2]
  rw [mul_assoc]
  rw [h1]
  rw [mul_one] -- hooray!
