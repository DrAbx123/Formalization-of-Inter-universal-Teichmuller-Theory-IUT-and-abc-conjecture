import Mathlib

open Polynomial
open NumberField

noncomputable section

namespace S2167Probe

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

example (p : Ideal (𝓞 K)) [p.IsPrime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p]
    [Finite (𝓞 L ⧸ P)] :
    ∃ σ : Gal(L/K), IsArithFrobAt (𝓞 K) σ P := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI : Algebra.IsInvariant (𝓞 K) (𝓞 L) Gal(L/K) := Algebra.isInvariant_of_isGalois (𝓞 K) K L (𝓞 L)
  exact IsArithFrobAt.exists_of_isInvariant (𝓞 K) Gal(L/K) P

end S2167Probe
