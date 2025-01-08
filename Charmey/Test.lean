import Mathlib

theorem Example1 {M : Type*} [Monoid M] (a b c : M) (h1 : a * b = 1) (h2 : c * a = 1) :
    b = c := by
  rw [← one_mul b] -- "one_mul b" is a proof that `1 * b = b`
  rw [← h2]
  rw [mul_assoc]
  rw [h1]
  rw [mul_one] -- hooray!

theorem Example2 {M : Type*} [Monoid M] (a b c : M) (h1 : a * b = 1) (h2 : c * a = 1) :
    b = c := by
  have h3 : b = c * a * b := by
    rw [h2, one_mul]
  have h4 : c * a * b = c := by
    rw [mul_assoc, h1, mul_one]
  rw [h3, h4]

-- theorem Example3 {M : Type*} [CommMonoid M] (a b c : M) :
--     a * (b * c) = b * (c * a) := by
--   by_cases h : a = 1
--   · sorry
--   · sorry

-- #check 2 + 2
-- #check 2 + 2 = 4
-- #check (by decide : 2 + 2 = 4)
