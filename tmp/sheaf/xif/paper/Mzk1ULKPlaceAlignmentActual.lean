/- U-R 索引对齐（source 侧）:
  a) nativeBadToFPlace = (nativeBadLift T).lift b（source selection）及其 comap;
  b) 在语法相等 F-位点上, orderAtFPlace 与 qVFamAt 的 order 相等（用 S1413 parameter_order_congr）;
  c) 剩余 lift 的 Σ e f 计数（Mathlib sum_ramification_inertia，见下一批；本文件先给 b 与选择链接）。 -/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.S1413SourceKPlaceQComparisonActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULKPlaceAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 选定 F-位的 q-parameter order（source selection 的 c_b）。 -/
noncomputable def cSelected (b : Bad (nativePlaceSelection T)) : ℕ :=
  (qVFamAt T (nativeBadToFPlace T b) (by
    rw [nativeBadToFPlace_comap T b]; exact b.2)).order

/-- 在语法相等的 F-位点上，orderAtFPlace 等于 cSelected（S1413 parameter_order_congr）。 -/
theorem orderAtFPlace_eq_cSelected
    (b : Bad (nativePlaceSelection T))
    (P : Ideal (𝓞 (T.arithmetic.F)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F)))
    (hplace : badFPlaceOfIdeal T P hP = nativeBadToFPlace T b) :
    orderAtFPlace T b P hP = cSelected T b := by
  unfold orderAtFPlace cSelected
  -- hp/hq: the two places are bad (both comap to b.1)
  have hp : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
      (badFPlaceOfIdeal T P hP) ∈ (nativePlaceSelection T).V_mod_bad := by
    rw [badFPlaceOfIdeal_comap T P hP]; exact b.2
  have hq : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
      (nativeBadToFPlace T b) ∈ (nativePlaceSelection T).V_mod_bad := by
    rw [nativeBadToFPlace_comap T b]; exact b.2
  exact parameter_order_congr (T := T) hp hq hplace

/-- cSelected 的定义式（用于 O(1) 展开）。 -/
theorem cSelected_def (b : Bad (nativePlaceSelection T)) :
    cSelected T b = (qVFamAt T (nativeBadToFPlace T b) (by
      rw [nativeBadToFPlace_comap T b]; exact b.2)).order := rfl

#print axioms orderAtFPlace_eq_cSelected
#print axioms cSelected_def

end LeanFormal.IUT.XiFPaper.Mzk1ULKPlaceAlignmentActual
