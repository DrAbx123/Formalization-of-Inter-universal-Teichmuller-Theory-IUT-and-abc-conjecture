/- M_paper_v2 的 per-b 分解（kurt J1-M-scale 对接）:
  MpaperB b := (1/(2l)) * ((1/[F:Q]) * Σ_{P|b} f_P·c_P·log p_P)
  M_paper_v2 = Σ_b MpaperB b（Finset.sum 分解，rfl 级）。
  ord_P(q)=e_P·ord_b(q) 的 further Fmod 化简见下一批 Mzk1ULOrdFiberTowerActual
  （依赖 Ideal.ramificationIdx'_algebra_tower + fiber_sum_ef）。 -/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1ULFiberSumActual
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1ULQSelectedActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQSelectedActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 单个 b 的 M_paper 贡献（Q 尺度 /(2l)）。 -/
noncomputable def MpaperB (b : Bad (nativePlaceSelection T)) : ℝ :=
  (1 / (2 * (l.value : ℝ))) *
    ((1 / (Module.finrank ℚ (T.arithmetic.F) : ℝ)) *
      ∑ x ∈ (IsDedekindDomain.primesOverFinset
          (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
          Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ)))

/-- M_paper_v2 = Σ_b MpaperB b。 -/
theorem M_paper_v2_eq_sum_MpaperB :
    M_paper_v2 (T := T) = ∑ b : Bad (nativePlaceSelection T), MpaperB (l := l) T b := by
  rw [LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual.M_paper_v2_eq_sum_Qb_div (T := T)]
  apply Finset.sum_congr rfl
  intro b _
  unfold MpaperB LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual.Qb
  rw [div_eq_mul_inv, one_div]
  ring

/-- MpaperB 非负。 -/
theorem MpaperB_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ MpaperB (l := l) T b := by
  unfold MpaperB
  apply mul_nonneg
  · apply div_nonneg (by norm_num) (by positivity)
  · apply mul_nonneg
    · apply div_nonneg (by norm_num) (by positivity)
    · apply Finset.sum_nonneg
      intro x _
      exact fiberTerm_nonneg T b x.1 x.2

#print axioms M_paper_v2_eq_sum_MpaperB
#print axioms MpaperB_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual