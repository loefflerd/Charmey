import Mathlib

/-- A quiver with two vertices and `n` arrows between them. -/
def TwoVertexQuiver (n : ℕ) : Quiver (Fin 2) where
  Hom a b := match (a, b) with
  | (0, 0) => Empty -- or `Fin 0` if you prefer
  | (0, 1) => Empty
  | (1, 0) => Empty
  | (1, 1) => Fin n -- canonical type with `n` vertices, identified with {0, ..., n-1}

variable {ι : Type*} (Q : Quiver ι) (𝕜 : Type*) [Field 𝕜] (V : ι → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

/-- A `𝕜`-linear representation of the quiver `Q` on the family of vector spaces `V`. -/
structure Quiver.Representation where
  f : ∀ i j, Q.Hom i j → (V i →ₗ[𝕜] V j)

#check Quiver.Representation Q 𝕜 V
#check Q.Representation 𝕜 V
