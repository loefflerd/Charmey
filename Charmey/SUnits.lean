import Mathlib
/-!
# Example file for S-units
-/

open IsDedekindDomain

/- Define a bunch of variables. -/
variable {R : Type} [CommRing R] [IsDedekindDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-!
## Stuff about S-integers
-/

/-- If `S` is the empty set, then the `S`-integers are the minimal `R`-subalgebra of `K` (which is
just `R` itself). -/
lemma set_integer_empty : (∅ : Set (HeightOneSpectrum R)).integer K = ⊥ := sorry

/-- If `S` is the whole set of places of `K`, then the `S`-integers are the whole of `K`. -/
lemma set_integer_top : (Set.univ : Set (HeightOneSpectrum R)).integer K = ⊤ := sorry

/-!
## Stuff about S-units
-/

/-- If `S` is the whole set of places of `K`, then the `S`-units are the whole of `Kˣ`. -/
lemma set_unit_univ : (Set.univ : Set (HeightOneSpectrum R)).unit K = ⊤ := by
  simp [← Subgroup.coe_eq_univ]

/-- If `S` is the empty set, then the `S`-units are just `Rˣ`, embedded in `K`. -/
def set_unit_empty_equiv : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).integer K := sorry

/-- The map `Kˣ → ℤ` given by the valuation `v`.  -/
noncomputable def IsDedekindDomain.HeightOneSpectrum.unitsHom : Kˣ →* Multiplicative ℤ where
  toFun x := WithZero.unzero (v.valuation.ne_zero_of_unit x)
  map_one' := by simp [WithZero.unzero_coe]; rfl
  map_mul' x y := by simp [WithZero.unzero_mul]

lemma IsDedekindDomain.HeightOneSpectrum.unitsHom_apply (x : Kˣ) :
    v.unitsHom x = v.valuation x.val := by
  simp [unitsHom, WithZero.coe_unzero]

/-- The map `Kˣ → ∏ v ∈ S, ℤ` given by the product of all the valuations at the places `S`. -/
noncomputable def Set.unitsProdHom (S : Set (HeightOneSpectrum R)) :
    Kˣ →* (S → Multiplicative ℤ) where
  toFun x v := HeightOneSpectrum.unitsHom v.1 x
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
