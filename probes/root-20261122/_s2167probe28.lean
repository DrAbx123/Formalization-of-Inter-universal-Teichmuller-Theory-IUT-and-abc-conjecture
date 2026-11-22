import tmp.sheaf.xif.paper.S2132FrobCycleActual
import Mathlib.RingTheory.Frobenius

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Polynomial
open NumberField

namespace S2167Probe

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

example (sigma : Gal(L/K)) (b : RingOfIntegers L) :
    (sigma • b : RingOfIntegers L) =
      (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
       sigma • b : RingOfIntegers L) := by
  apply Subtype.ext
  change (sigma • (b : L)) = ((galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma b : L)
  exact (algebraMap_galRestrict_apply (RingOfIntegers K) sigma b).symm

example : Algebra.IsInvariant (RingOfIntegers K) (RingOfIntegers L) Gal(L/K) := by
  refine ⟨fun b hb => ?_⟩
  have hb' : ∀ g : Gal(L/K),
      (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
       g • b : RingOfIntegers L) = b := by
    intro g
    rw [← show (g • b : RingOfIntegers L) =
      (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
       g • b : RingOfIntegers L) from by
      apply Subtype.ext
      change (g • (b : L)) = ((galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) g b : L)
      exact (algebraMap_galRestrict_apply (RingOfIntegers K) g b).symm]
    exact hb g
  exact (Algebra.isInvariant_of_isGalois (RingOfIntegers K) K L (RingOfIntegers L)).1 b hb'

example (P : Ideal (RingOfIntegers L)) [P.IsPrime] [Finite (RingOfIntegers L ⧸ P)] :
    ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P := by
  haveI : Algebra.IsInvariant (RingOfIntegers K) (RingOfIntegers L) Gal(L/K) := by
    refine ⟨fun b hb => ?_⟩
    have hb' : ∀ g : Gal(L/K),
        (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
          IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
         g • b : RingOfIntegers L) = b := by
      intro g
      rw [← show (g • b : RingOfIntegers L) =
        (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
          IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
         g • b : RingOfIntegers L) from by
        apply Subtype.ext
        change (g • (b : L)) = ((galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) g b : L)
        exact (algebraMap_galRestrict_apply (RingOfIntegers K) g b).symm]
      exact hb g
    exact (Algebra.isInvariant_of_isGalois (RingOfIntegers K) K L (RingOfIntegers L)).1 b hb'
  exact IsArithFrobAt.exists_of_isInvariant (RingOfIntegers K) Gal(L/K) P

end S2167Probe
end
