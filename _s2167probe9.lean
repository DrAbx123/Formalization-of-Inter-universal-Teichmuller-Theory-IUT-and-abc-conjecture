import Mathlib

open Polynomial
open NumberField

noncomputable section

namespace S2167Probe

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

example :
    letI : MulSemiringAction Gal(L/K) (𝓞 L) := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    SMulCommClass Gal(L/K) (𝓞 K) (𝓞 L) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  refine ⟨fun σ a b => ?_⟩
  apply RingOfIntegers.coe_injective
  change (algebraMap (𝓞 L) L) ((galRestrict (𝓞 K) K L (𝓞 L) σ) (a • b)) =
    (algebraMap (𝓞 L) L) (a • (galRestrict (𝓞 K) K L (𝓞 L) σ) b)
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
  rw [AlgEquiv.commutes]
  rfl

end S2167Probe
