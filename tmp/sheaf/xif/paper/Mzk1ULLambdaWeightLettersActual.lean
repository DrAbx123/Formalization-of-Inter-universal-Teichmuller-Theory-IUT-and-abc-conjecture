/- (B) 终裁: λ 权字母 + Qb per-b 对账（hstepVIII λ 版接口，不 fake）。
  Qb_b := (1/[F:Q]) Σ_{P|b} f_P c_P logp（无外层权）;
  qPilotMagnitudePaper_v2 = Σ_b Qb_b; M_paper_v2 = Σ_b Qb_b/(2l)。
  λ 权字母以显式参数接口 LambdaWeightLetters 给出（hlogdK/hsQraw/hM），
  待 hlogK/hsQ 的 λ 版真证落地后填入（不把 legacy native 权冒充 λ）。 -/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULLambdaWeightLettersActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- per-b 的 Q 贡献（无外层权，v2 的 fiber 和 /[F:Q]）。 -/
noncomputable def Qb (b : Bad (nativePlaceSelection T)) : ℝ :=
  (1 / (Module.finrank ℚ (T.arithmetic.F) : ℝ)) *
    ∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
        Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ))

/-- Qb 定义式。 -/
theorem Qb_def (b : Bad (nativePlaceSelection T)) : Qb (T := T) b = (1 / (Module.finrank ℚ (T.arithmetic.F) : ℝ)) * (∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach, ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) * Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ))) := rfl

/-- qPilotMagnitudePaper_v2 = Σ_b Qb_b。 -/
theorem qPilotMagnitudePaper_v2_eq_sum_Qb :
    qPilotMagnitudePaper_v2 (T := T) = ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b := by
  unfold qPilotMagnitudePaper_v2 Qb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [div_eq_mul_inv, mul_comm]

/-- M_paper_v2 = Σ_b Qb_b/(2l)。 -/
theorem M_paper_v2_eq_sum_Qb_div :
    M_paper_v2 (T := T) = ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b / (2 * (l.value : ℝ)) := by
  unfold M_paper_v2
  rw [qPilotMagnitudePaper_v2_eq_sum_Qb]
  rw [Finset.sum_div]

/-- λ 权字母接口（hlogdK/hsQraw/hstepVIII/H 的 λ 版形状；由 hlogK/hsQ 真证填入）。 -/
theorem lambda_letters_hstepVIII
    (w : Bad (nativePlaceSelection T) → ℝ) (D : Bad (nativePlaceSelection T) → ℝ)
    (S_ar logl logSleq dmod Qval M H lstar : ℝ)
    (hlogdK : (∑ b, w b * D b) ≤ S_ar + 2 * Real.log logl + 21)
    (hsQraw : (∑ b, w b) * logSleq ≤ 2 * dmod * S_ar + 5 + Real.log logl)
    (hstepVIII : H ≤ LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa logl *
      ((1 + 12 * dmod / logl) * S_ar + 2 * Real.log logl + 56
        - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL logl * Qval + (20 / 3) * lstar) - M)
    (hM : M = Qval / (2 * logl)) :
    H ≤ LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa logl *
      ((1 + 12 * dmod / logl) * S_ar + 2 * Real.log logl + 56
        - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL logl * Qval + (20 / 3) * lstar) - M := hstepVIII

#print axioms qPilotMagnitudePaper_v2_eq_sum_Qb
#print axioms M_paper_v2_eq_sum_Qb_div
#print axioms lambda_letters_hstepVIII

end LeanFormal.IUT.XiFPaper.Mzk1ULLambdaWeightLettersActual