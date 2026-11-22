/- Qb per-b 分解（轻件，kurt hM_lambda ASAP）:
  Qb b := (1/[F:Q])·Σ_{P|b} f_P·c_P·log p_P;
  qPilotMagnitudePaper_v2 = Σ_b Qb b; M_paper_v2 = Σ_b Qb b/(2l)。
  donor: Mzk1ULQPilotMagnitudeV2Actual（qPilotMagnitudePaper_v2 定义）;
  Mzk1HT82PaperWeightDiffActual.underIntGen。 -/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- per-b 的 Q 贡献（无外层权）。 -/
noncomputable def Qb (b : Bad (nativePlaceSelection T)) : ℝ :=
  (1 / (Module.finrank ℚ (T.arithmetic.F) : ℝ)) *
    ∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
        Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ))

/-- qPilotMagnitudePaper_v2 = Σ_b Qb_b。 -/
theorem qPilotMagnitudePaper_v2_eq_sum_Qb :
    qPilotMagnitudePaper_v2 (T := T) = ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b := by
  unfold qPilotMagnitudePaper_v2 Qb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [div_eq_mul_inv, one_div]
  ring

/-- M_paper_v2 = Σ_b Qb_b/(2l)。 -/
theorem M_paper_v2_eq_sum_Qb_div :
    M_paper_v2 (T := T) =
      ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b / (2 * (l.value : ℝ)) := by
  unfold M_paper_v2
  rw [qPilotMagnitudePaper_v2_eq_sum_Qb]
  congr 1
  rw [Finset.sum_div]

#print axioms qPilotMagnitudePaper_v2_eq_sum_Qb
#print axioms M_paper_v2_eq_sum_Qb_div

end LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual