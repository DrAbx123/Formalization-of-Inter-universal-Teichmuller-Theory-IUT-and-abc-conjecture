/- R1 fiber-prime consistency: Qb_b = cPFullFiber_b * log p_b
   (hypothesis: all P in the b-fiber have underIntGen natAbs = qVFamTensorP T b). -/
import tmp.sheaf.xif.paper.Mzk1ULR0FullFiberActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR1CPrimeFiberActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Paper full-fiber coefficient: (1/[F:Q]) Sum_{P|b} f_P * orderAtFPlace P. -/
noncomputable def cPFullFiber (b : Bad (nativePlaceSelection T)) : Real :=
  (1 / (Module.finrank ℚ (T.arithmetic.F) : Real)) *
    ∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real))

/-- Fiber-prime consistency implies Qb = cPFullFiber * log p. -/
theorem Qb_eq_cPFullFiber_mul_logp (b : Bad (nativePlaceSelection T))
    (hprime : ∀ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      (underIntGen (K := T.arithmetic.F) x.1).natAbs = qVFamTensorP T b) :
    Qb (T := T) b = cPFullFiber (l := l) T b * Real.log (qVFamTensorP T b : Real) := by
  unfold Qb cPFullFiber
  have hlog : ∀ x ∈ (IsDedekindDomain.primesOverFinset
      (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : Real) =
        Real.log (qVFamTensorP T b : Real) := by
    intro x hx
    rw [hprime x hx]
  calc (1 / (Module.finrank ℚ (T.arithmetic.F) : Real)) *
        ∑ x ∈ (IsDedekindDomain.primesOverFinset
            (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
          ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real) *
            Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : Real))
      = (1 / (Module.finrank ℚ (T.arithmetic.F) : Real)) *
        (∑ x ∈ (IsDedekindDomain.primesOverFinset
            (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
          ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real))) *
          Real.log (qVFamTensorP T b : Real) := by
        have hterm : ∀ x ∈ (IsDedekindDomain.primesOverFinset
            (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
            ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real) *
              Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : Real)) =
            ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real)) *
              Real.log (qVFamTensorP T b : Real) := by
          intro x hx
          rw [hlog x hx]
        rw [Finset.sum_congr rfl hterm]
        rw [← Finset.sum_mul]
        ring
    _ = (1 / (Module.finrank ℚ (T.arithmetic.F) : Real)) *
        (∑ x ∈ (IsDedekindDomain.primesOverFinset
            (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
          ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real))) *
          Real.log (qVFamTensorP T b : Real) := rfl

#print axioms Qb_eq_cPFullFiber_mul_logp

end LeanFormal.IUT.XiFPaper.Mzk1ULR1CPrimeFiberActual