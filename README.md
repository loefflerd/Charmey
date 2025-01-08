# Formalising mathematics in Lean

Mini-course at _Swiss-French workshops in algebraic geometry_, 14th edition, Charmey (FR), January 13-17, 2025

## Lecture 1: Our first Lean theorem

- Open https://live.lean-lang.org/

- Copy and paste the following:

```lean
import Mathlib

/-- If an element of a monoid has a right and a left inverse, the two inverses are equal. -/
theorem Example1
    (M : Type) [Monoid M] (a b c : M)
    (h1 : a * b = 1) (h2 : c * a = 1) : 
    b = c := by
  rw [← one_mul b]
  rw [← h2]
  rw [mul_assoc]
  rw [h1]
  rw [mul_one] -- hooray!
```
