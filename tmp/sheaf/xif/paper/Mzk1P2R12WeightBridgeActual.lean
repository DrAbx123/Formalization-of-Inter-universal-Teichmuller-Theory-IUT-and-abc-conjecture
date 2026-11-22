import tmp.sheaf.xif.paper.Mzk1P2ArchWeightAlignmentActual
import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
import tmp.sheaf.xif.paper.Mzk1P2QNativeSourceArrowActual
import Mathlib.Tactic

/-! # P2: R1.2 weight bridge

The actual R1.2 coefficient c_b = qhat_b/lambda_b, its weighted log term, and
the theta allowed-image inclusion are combined here.  The native-q real reading
identification remains the explicit P2QNativeReadingGap.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2R12WeightBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeSourceArrowActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R1.2 weighted local term: s1915 degree times log norm of the actual
coefficient c_b. -/
noncomputable def p2R12WeightTerm (b : Bad (nativePlaceSelection T)) : Real :=
  (s1915LocalDegree T b : Real) * Real.log ‖p2Coefficient T b‖

/-- The R1.2 weighted sum is exactly p2WeightedDetLog. -/
theorem p2R12WeightSum_eq_p2WeightedDetLog :
    (∑ b : Bad (nativePlaceSelection T), p2R12WeightTerm T b) =
      p2WeightedDetLog T := rfl

/-- Each R1.2 weighted term is nonpositive. -/
theorem p2R12WeightTerm_nonpos (b : Bad (nativePlaceSelection T)) :
    p2R12WeightTerm T b ≤ 0 := by
  unfold p2R12WeightTerm
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
  exact Real.log_nonpos (norm_nonneg _)
    (p2Coefficient_norm_le_one T b)

/-- The R1.2 weighted sum is nonpositive. -/
theorem p2R12WeightSum_nonpos :
    (∑ b : Bad (nativePlaceSelection T), p2R12WeightTerm T b) ≤ 0 := by
  apply Finset.sum_nonpos
  intro b _
  exact p2R12WeightTerm_nonpos T b

/-- Actual R1.2 expansion: qhat = lambda * c. -/
theorem p2R12_qhat_expansion (b : Bad (nativePlaceSelection T)) :
    c0QHat T b = rootThetaFieldLambda T b * p2Coefficient T b :=
  p2QHat_eq_lambda_mul_coefficient T b

/-- Native q reading gap remains the exact missing statement. -/
def p2R12NativeReadingGap : Prop := P2QNativeReadingGap T

def p2R12WeightBridgeMissing : List String :=
  [ "native q real reading = root qhat log norm (P2QNativeReadingGap)",
    "global arch log = p2WeightedDetLog (arch alignment hypothesis)",
    "theta allowed-image inclusion: dependency Mzk1P2ThetaAllowedImageActual currently red; not used" ]

theorem p2R12WeightBridgeMissing_length :
    p2R12WeightBridgeMissing.length = 3 := rfl

#check p2R12WeightTerm
#check p2R12WeightSum_eq_p2WeightedDetLog
#check p2R12WeightTerm_nonpos
#check p2R12WeightSum_nonpos
#check p2R12_qhat_expansion
#check p2R12WeightBridgeMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2R12WeightBridgeActual
end
