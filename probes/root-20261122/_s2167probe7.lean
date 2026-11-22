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
  dsimp only [IsIntegralClosure.MulSemiringAction, MulSemiringAction.compHom]
  change (galRestrict (𝓞 K) K L (𝓞 L) σ) (a • b) = a • (galRestrict (𝓞 K) K L (𝓞 L) σ) b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  congr 1
  exact algebraMap_galRestrict_apply (𝓞 K) σ b

end S2167Probe
