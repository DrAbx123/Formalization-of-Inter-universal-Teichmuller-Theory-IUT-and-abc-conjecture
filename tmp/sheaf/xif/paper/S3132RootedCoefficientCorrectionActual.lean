import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import tmp.sheaf.xif.paper.S826CNormOrderRamificationActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.S3131CoefficientReductionActual

namespace LeanFormal.IUT.XiFPaper.S3132RootedCoefficientCorrectionActual

/-!
# STEP 0 prior-art: QVFamNormalizedCoefficient_eq_order_iff_e_eq_one|qVFamPaperRootCoefficient|S3131PaperRootCoefficient_eq_ramification_mul_rootHalf -> hits in S826CNormOrderRamificationActual:64, S3131CoefficientReductionActual:150, RootNormalizedContainmentActual:57, QVFamRootFactorCorrectionActual:56 -> REUSE (no re-proof).

# H3 (coefficient identification hc) is NOT paper-faithful in general

Prior art: S3131CoefficientReductionActual:145-161 (Task-13 correction) proves
`qVFamPaperRootCoefficient = e * rootHalfCoefficient` under the normalized norm
relation with relative ramification index e, and S826CNormOrderRamificationActual:64
proves `qVFamNormalizedCoefficient = order ↔ e = 1`.
Consequently the coefficient identification hc (rootHalfCoefficient =
paperRootCoefficientFamily, i.e. order/(2l)) holds exactly at e = 1; for e ≠ 1 the
tree records the paper-faithful numerical choice as rootHalfCoefficient (c_norm/(2l)),
NOT the order/(2l) family.  Our sharp residual (R2) already uses
rootHalfCoefficient directly, so it is paper-faithful and does NOT need hc; hc only
serves the paper-coefficient formula route as an e = 1 specialization.
-/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The paper root coefficient family is e times the paper-faithful rooted
half-coefficient (Task-13 correction, reused from S3131CoefficientReduction:150). -/
theorem paperRootCoefficientFamily_eq_e_mul_rootHalf
    (e : ℝ) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) :
    paperRootCoefficientFamily T b =
      fun _ => e * rootHalfCoefficient (l := l) T b () := by
  funext i
  cases i
  show qVFamPaperRootCoefficient (l := l) T b =
    e * rootHalfCoefficient (l := l) T b ()
  exact S3131PaperRootCoefficient_eq_ramification_mul_rootHalf
    (l := l) T b e hepos hcomp

/-- At e = 1 the paper coefficient family equals the paper-faithful rooted
half-coefficient (the only case where hc can hold). -/
theorem paperRootCoefficientFamily_eq_rootHalf_of_e_one
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b 1) :
    paperRootCoefficientFamily T b = rootHalfCoefficient (l := l) T b := by
  rw [paperRootCoefficientFamily_eq_e_mul_rootHalf (l := l) T b 1 one_pos hcomp]
  funext i
  exact one_mul (rootHalfCoefficient (l := l) T b i)

/-- Exact iff: the coefficient identification (c_norm = order) holds exactly when
e = 1, under the normalized norm relation. -/
theorem normalizedCoefficient_eq_order_iff_e_one
    (e : ℝ) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : ℝ) ↔ e = 1 :=
  qVFamNormalizedCoefficient_eq_order_iff_e_eq_one (l := l) T b e hepos hcomp

#check paperRootCoefficientFamily_eq_e_mul_rootHalf
#check paperRootCoefficientFamily_eq_rootHalf_of_e_one
#check normalizedCoefficient_eq_order_iff_e_one

end LeanFormal.IUT.XiFPaper.S3132RootedCoefficientCorrectionActual
end