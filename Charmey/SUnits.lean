import Mathlib
/-!
# Example file for S-units
-/

variable {R : Type} [CommRing R] [IsDedekindDomain R] (S : Set (IsDedekindDomain.HeightOneSpectrum R)) (K : Type) [Field K]  [Algebra R K] [IsFractionRing R K]

#check Set.integer_eq S K

variable (v : IsDedekindDomain.HeightOneSpectrum R)

#check v.valuation


noncomputable def unitsMap :
    Additive (S.unit K) →+ (S → ℤ) where
  toFun x v := sorry -- IsDedekindDomain.HeightOneSpectrum.valuation v x
