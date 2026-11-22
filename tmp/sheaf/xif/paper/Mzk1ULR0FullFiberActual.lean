/- R0.2 full-fiber (sophie co-sign): Qb_b = (1/[F:Q]) * Sum_{P|b} f_P * order_P * log p_P,
   M_paper_v2 = (1/(2l)) Sum_b Qb_b, q_P5 = -M_paper_v2.
   c_P per P = orderAtFPlace P (NOT cSelected for all P; selected lift only via
   Mzk1ULKPlaceAlignmentActual.orderAtFPlace_eq_cSelected for the selected P).
   paper: IV L1324-1333/1206-1235/1436-1501; IV L1359-1364; III L872-877/932.
   donors: Mzk1ULQPilotMagnitudeV2Actual.{orderAtFPlace,qPilotMagnitudePaper_v2,M_paper_v2};
           Mzk1ULQbVecActual.{Qb,qPilotMagnitudePaper_v2_eq_sum_Qb,M_paper_v2_eq_sum_Qb_div};
           Mzk1ULFiberSumActual.{fiber_sum_ef,qPilotMagnitudePaper_v2_expand};
           Mzk1ULOrdFiberTowerActual.{MpaperB,M_paper_v2_eq_sum_MpaperB};
           Mzk1URC2AssemblyActual.{qP5,qP5_def}. -/
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.Mzk1URC2AssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0FullFiberActual

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
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual
open LeanFormal.IUT.XiFPaper.Mzk1URC2AssemblyActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R0.2: Qb_b 是 paper 的 (1/[F:Q])*Sum_{P|b} f_P*order_P*log p_P（rfl, Qb 定义）。 -/
theorem Qb_eq_paper_fullFiber (b : Bad (nativePlaceSelection T)) :
    Qb (T := T) b =
      (1 / (Module.finrank ℚ (T.arithmetic.F) : Real)) *
        ∑ x ∈ (IsDedekindDomain.primesOverFinset
            (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
          ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real) *
            Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : Real)) := rfl

/-- R0.2: M_paper_v2 = (1/(2l)) Sum_b Qb_b。 -/
theorem Mpaper_eq_half_sum_Qb :
    M_paper_v2 (l := l) T =
      (1 / (2 * (l.value : Real))) * ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b := by
  rw [M_paper_v2_eq_sum_Qb_div (T := T)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [div_eq_mul_inv]
  ring

/-- R0.2: q_P5 = -M_paper_v2 (definitional; no URC2 instance binders)。 -/
theorem qP5_eq_neg_Mpaper : qP5 (l := l) T = -M_paper_v2 (l := l) T := by
  unfold qP5
  rfl

#print axioms Qb_eq_paper_fullFiber
#print axioms Mpaper_eq_half_sum_Qb
#print axioms qP5_eq_neg_Mpaper

end LeanFormal.IUT.XiFPaper.Mzk1ULR0FullFiberActual