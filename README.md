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

## Lecture 2: Proofs and tactics

See the example file https://github.com/loefflerd/Charmey/blob/main/Charmey/Ideals.lean in this GitHub project.

### Useful tactics

- `rw` (rewrite): replace sub-expressions of the goal. If `h` is a proof that `X = Y`, then `rw [h]` replaces all `X`'s in the goal with `Y`'s, and `rw [<- h]` replaces all `Y`'s with `X`'s. Also `rw [...] at hyp` to rewrite in a hypothesis (not the goal).
- `rw?`: search for rewrites that work.
- `use`: if the goal is that `∃ x` satisfying some condition, then `use q` will change the goal to proving that `x = q` works.
- `obtain`: if you have a hypothesis that `∃ x` satisfying some condition, then `obtain` gets a specific `x` satisfying that condition
- `have`: "I claim that..." -- introduce a claim, prove the claim, and then show that the claim implies the main goal.
- `suffices`: "It suffices to prove that..." -- introduce a claim, prove that it implies the goal, and then prove the claim.
- `assumption`: the goal is already there in the context
- `tauto`: the goal follows from the assumptions by trivial logic (understands `and`, `or`, `not` and `implies`)
- `apply`: use a theorem from the library -- if `P` is a theorem stating that the goal is true, then `apply P` closes the main goal and opens new goals for the hypotheses of `P` (if any). `apply?` searches for theorems that imply the goal.
- `induction`: if `n` is a natural number variable, then `induction n with ...` sets up a proof by induction on `n`.

See https://github.com/madvorak/lean4-tactics/blob/main/README.md for a slightly longer list.
