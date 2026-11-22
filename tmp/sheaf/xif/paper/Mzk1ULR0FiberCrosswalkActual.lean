/- R0 step 3: full-fiber same-j crosswalk
     cPFullFiber_b = thetaLamWeight_b * cP_local_b.
   Route inputs (route 4.4/R0):
   - TateCurveComparison.realizesCurve + q_P*j(q_P) unit gives v_P(q_P) = -v_P(j),
     i.e. a single value vsel on the fiber, and field_moduli_spec (SourceClauseA)
     gives the per-P relation order_P = e_rel(P|b) * vsel;
   - fiber_sum_ef (Mzk1ULFiberSumActual) gives sum_{P|b} e_rel f_rel = [F:Fmod];
     with f_P^abs = f_b^abs * f_rel this yields hsum below;
   - hprime is used ONLY to extract log p (fiber-prime consistency), not for this crosswalk.
   cP_local_b = f_b^abs * vsel / lamWeight_b (paper value normalized by the local degree);
   thetaLamWeight_b = lamWeight_b / dModF_b with dModF = [Fmod:Q]. -/
import tmp.sheaf.xif.paper.Mzk1ULR1MpaperBWeightActual
import tmp.sheaf.xif.paper.Mzk1ULFiberSumActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1ULR0RealDictionaryActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0FiberCrosswalkActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULFiberSumActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R0 step 3 crosswalk: single-j value + per-P e-relation + fiber sum gives
    cPFullFiber_b = thetaLamWeight_b * cP_local_b. -/
theorem cPFullFiber_eq_thetaLamWeight_mul_cP
    (b : Bad (nativePlaceSelection T)) (vsel : Real)
    (horder : ∀ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      (orderAtFPlace T b x.1 x.2 : Real) =
        (Ideal.ramificationIdx' (b.1.maximalIdeal.asIdeal) x.1 : Real) * vsel)
    (hsum : (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : Real) *
          (Ideal.ramificationIdx' (b.1.maximalIdeal.asIdeal) x.1 : Real))) =
      (b.1.maximalIdeal.asIdeal.inertiaDeg ℤ : Real) *
        (Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) : Real))
    (hcP : cP (l := l) T b =
      (b.1.maximalIdeal.asIdeal.inertiaDeg ℤ : Real) * vsel / lamWeight T b)
    (hlam : lamWeight T b ≠ 0)
    (hdmod : dModF T ≠ 0)
    (hFQ : (Module.finrank ℚ (T.arithmetic.F) : Real) ≠ 0)
    (hFF : (Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) : Real) ≠ 0)
    (hdeg : (Module.finrank ℚ (T.arithmetic.F) : Real) =
      (Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) : Real) * dModF T) :
    cPFullFiber (l := l) T b = thetaLamWeight T b * cP (l := l) T b := by
  unfold cPFullFiber thetaLamWeight
  rw [hcP]
  have hsum' : (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real))) =
      (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : Real) *
          (Ideal.ramificationIdx' (b.1.maximalIdeal.asIdeal) x.1 : Real))) * vsel := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [horder x hx]
    ring
  rw [hsum', hsum, hdeg]
  field_simp [hlam, hdmod, hFF]

#print axioms cPFullFiber_eq_thetaLamWeight_mul_cP

end LeanFormal.IUT.XiFPaper.Mzk1ULR0FiberCrosswalkActual