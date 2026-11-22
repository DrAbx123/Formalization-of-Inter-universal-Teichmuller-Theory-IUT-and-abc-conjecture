/- D2 的 Q_selected（route L577-579: 进入当前 initial Θ-data 的选定位之和）:
  选定 F-位 = nativeBadToFPlace T b（source selection）。
  QSelected := (1/[F:Q]) Σ_b Σ_{P over b.1} [P = selectedIdeal b]·f_P·c_P·log p_P
  （用 if 选择，不预设 selectedIdeal ∈ fiber 的桥；其 membership 由 nativeBadToFPlace_comap 下一批证）。
  hMinusQ := 补集和; 恒等式 qPilotMagnitudePaper_v2 = QSelected + hMinusQ（逐点 if 分解）。
  注: 不是 legacy qPilotMagnitudePaper（其 K-side 权口径不同）。 -/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULQSelectedActual

open NumberField
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 选定 F-位（source selection）。 -/
noncomputable def selectedFPlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.F :=
  nativeBadToFPlace T b

/-- 选定 F-位的素理想。 -/
noncomputable def selectedIdeal (b : Bad (nativePlaceSelection T)) :
    Ideal (𝓞 (T.arithmetic.F)) :=
  (selectedFPlace T b).maximalIdeal.asIdeal

/-- 一个 fiber 项（f_P·c_P·log p_P）。 -/
noncomputable def fiberTerm (b : Bad (nativePlaceSelection T))
    (P : Ideal (𝓞 (T.arithmetic.F)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) : ℝ :=
  (P.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b P hP : ℝ) *
    Real.log ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ)

/-- Q_selected（选定位之和，paper 口径）。 -/
noncomputable def QSelected : ℝ :=
  (∑ b : Bad (nativePlaceSelection T),
    ∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      if x.1 = selectedIdeal T b then fiberTerm T b x.1 x.2 else 0) /
    (Module.finrank ℚ (T.arithmetic.F) : ℝ)

/-- h − Q_selected 的补集部分。 -/
noncomputable def hMinusQ : ℝ :=
  (∑ b : Bad (nativePlaceSelection T),
    ∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      if x.1 = selectedIdeal T b then 0 else fiberTerm T b x.1 x.2) /
    (Module.finrank ℚ (T.arithmetic.F) : ℝ)

/-- fiberTerm 非负。 -/
theorem fiberTerm_nonneg (b : Bad (nativePlaceSelection T))
    (P : Ideal (𝓞 (T.arithmetic.F)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) :
    0 ≤ fiberTerm T b P hP := by
  unfold fiberTerm
  have h1 : (0 : ℝ) ≤ (P.inertiaDeg ℤ : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (orderAtFPlace T b P hP : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ Real.log ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ) :=
    Real.log_natCast_nonneg _
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- Q_selected 非负。 -/
theorem QSelected_nonneg : 0 ≤ QSelected (T := T) := by
  unfold QSelected
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact fiberTerm_nonneg T b x.1 x.2
  · exact le_rfl

/-- hMinusQ 非负。 -/
theorem hMinusQ_nonneg : 0 ≤ hMinusQ (T := T) := by
  unfold hMinusQ
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact le_rfl
  · exact fiberTerm_nonneg T b x.1 x.2

/-- 全 fiber 分解: qPilotMagnitudePaper_v2 = QSelected + hMinusQ（逐点 if 分解）。 -/
theorem qPilotMagnitudePaper_v2_eq_QSelected_add_hMinusQ :
    qPilotMagnitudePaper_v2 (T := T) = QSelected (T := T) + hMinusQ (T := T) := by
  unfold qPilotMagnitudePaper_v2 QSelected hMinusQ
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  unfold fiberTerm
  split_ifs with h <;> ring

#print axioms fiberTerm_nonneg
#print axioms QSelected_nonneg
#print axioms hMinusQ_nonneg
#print axioms qPilotMagnitudePaper_v2_eq_QSelected_add_hMinusQ

end LeanFormal.IUT.XiFPaper.Mzk1ULQSelectedActual