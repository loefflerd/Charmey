# Formalising mathematics in Lean

Mini-course at _Swiss-French workshops in algebraic geometry_, 14th edition, Charmey (FR), January 13-17, 2025

## Lecture 1: Our first Lean theorem

- Open https://live.lean-lang.org/

- Copy and paste the following:

```lean
import Mathlib

theorem Example1 (M : Type) [Monoid M] (a b c : M)
    (h1 : a * b = 1) (h2 : c * a = 1) : 
    b = c := by
  rw [← one_mul b]
  rw [← h2]
  rw [mul_assoc]
  rw [h1]
  rw [mul_one] -- hooray!
```

## Getting access to Lean

- Method 1: use https://live.lean-lang.org/ (as above)
- Method 2: follow the instructions at https://lean-lang.org/lean4/doc/quickstart.html.

If you use Method 2, then when you reach the step "*Set up Lean 4 Project*", I recommend you choose the option "Download an existing project" and use the URL for this Github page, https://github.com/loefflerd/Charmey. Then you will get a pre-prepared project with the examples from the lectures and a recent version of "Mathlib" already installed.

## Learning resources

- Mathematics in Lean (Avigad-Massot): https://leanprover-community.github.io/mathematics_in_lean/
- Mechanics of Proof (Macbeth): https://hrmacbeth.github.io/math2001/
- Natural Numbers Game (Buzzard): https://adam.math.hhu.de
