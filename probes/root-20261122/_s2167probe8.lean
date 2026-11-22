import Mathlib

open Polynomial
open NumberField

noncomputable section

namespace S2167Probe

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

example (σ : Gal(L/K)) (b : 𝓞 L) :
    letI : MulSemiringAction Gal(L/K) (𝓞 L) := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    (σ • b : 𝓞 L) = galRestrict (𝓞 K) K L (𝓞 L) σ b := rfl

example (σ : Gal(L/K)) (b : 𝓞 L) :
    letI : MulSemiringAction Gal(L/K) (𝓞 L) := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    (algebraMap (𝓞 L) L) (σ • b) = (galRestrict (𝓞 K) K L (𝓞 L) σ) b := by
  rw [show (σ • b : 𝓞 L) = galRestrict (𝓞 K) K L (𝓞 L) σ b from rfl]
  rfl

end S2167Probe
