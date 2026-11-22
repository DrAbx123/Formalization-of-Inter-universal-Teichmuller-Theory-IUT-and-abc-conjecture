/- C3-upper intermediate: hM_lambda (kurt), reusing david's DONE files.

Reuse:
* Mzk1ULQbVecActual (DONE 12:47:05): M_paper_v2_eq_sum_Qb_div : M_paper_v2 = Sum_b Qb_b/(2l);
* Mzk1ULThetaLamWeightPosActual (DONE 12:54:41): thetaLamWeight_pos,
  Qloc (T:=T) b, thetaLamWeight_mul_Qloc (T:=T) b : thetaLamWeight b * Qloc b = Qb b.
Local reparameterization only; global Qb/Q definitions unchanged.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1ULThetaLamWeightPosActual
import tmp.sheaf.xif.paper.Mzk1ULStepVIIILambdaActual
import tmp.sheaf.xif.paper.Mzk1ULHlogKHSULambdaStatementsActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKHMLambdaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- hM, per-term Qb form (david's identity). -/
theorem hM_lambda_div :
    LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (T := T) =
      ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b / (2 * (l.value : ℝ)) :=
  Mzk1ULQbVecActual.M_paper_v2_eq_sum_Qb_div (T := T)

/-- hM in the lambda-weighted form required by hstepVIII_of_collectionLayer_gen. -/
theorem hM_lambda :
    LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (T := T) =
      (∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T b * Qloc (T := T) b) / (2 * (l.value : ℝ)) := by
  rw [Finset.sum_div]
  have h : (∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T b * Qloc (T := T) b / (2 * (l.value : ℝ))) =
      ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b / (2 * (l.value : ℝ)) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [thetaLamWeight_mul_Qloc (T := T) b]
  rw [h]
  exact hM_lambda_div T

#print axioms hM_lambda_div
#print axioms hM_lambda

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKHMLambdaActual
end