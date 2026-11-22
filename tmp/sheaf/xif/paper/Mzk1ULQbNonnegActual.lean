/- Qb/Qloc 非负（kurt hQ0 用）:
  Qb b = (1/[F:Q])·Σ_{P|b} f_P·c_P·log p_P ≥ 0;
  Qloc b = Qb b / thetaLamWeight b ≥ 0（thetaLamWeight>0）。
  donor: Mzk1ULQbVecActual.Qb（DONE 12:47:05）、Mzk1ULThetaLamWeightPosActual.{Qloc,thetaLamWeight_pos}（DONE 12:54:41）。 -/
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1ULThetaLamWeightPosActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULQbNonnegActual

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
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Qb 非负。 -/
theorem Qb_nonneg (b : Bad (nativePlaceSelection T)) : 0 ≤ Qb (T := T) b := by
  unfold Qb
  apply mul_nonneg
  · apply div_nonneg (by norm_num) (by positivity)
  · apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · exact Real.log_natCast_nonneg _

/-- Qloc 非负（thetaLamWeight>0）。 -/
theorem Qloc_nonneg (b : Bad (nativePlaceSelection T)) : 0 ≤ Qloc (T := T) b := by
  unfold Qloc
  apply div_nonneg
  · exact Qb_nonneg T b
  · exact (thetaLamWeight_pos T b).le

#print axioms Qb_nonneg
#print axioms Qloc_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1ULQbNonnegActual
