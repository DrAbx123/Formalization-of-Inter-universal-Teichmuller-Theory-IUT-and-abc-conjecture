import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

/-! # S736: which qVFamNormalizedCoefficient does rootNormCoefficient use?

RootNormalizedContainmentActual opens QVFamNormalizedGeneratorSupplyActual, not
QVFamNormalizedCoefficientActual.  Therefore
  rootNormCoefficient = generator-supply spectral coefficient
                     = -log_b(norm generator),
NOT the paper order.  Consequently rootHalfCoefficient = c_norm/(2l) is the
spectral c_norm/(2l), and S706 perBThetaHullLog (which uses rootHalfCoefficient)
also carries this c_norm.  The paper-order identification is an exact gap.
No equality is asserted. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S736RootNormCoefficientAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The opened family is the generator-supply spectral coefficient. -/
theorem rootNormCoefficient_eq_generatorSupply :
    rootNormCoefficient (l := l) T b =
      fun _ => QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient (l := l) T b := by
  funext i
  rfl

/-- The paper-order coefficient is a different name/definition. -/
theorem paperOrderCoefficient_eq :
    QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient (l := l) T b =
      ((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) := by
  exact QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient_eq_order (l := l) T b

/-- Exact identification needed: the spectral c_norm equals the paper order. -/
def S736PaperOrderGap : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient (l := l) T b =
    ((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real)

theorem S736PaperOrderGapRequired : Prop :=
  S736PaperOrderGap (l := l) T b

/-- Conditional statement: if the spectral c_norm equals paper order, then
rootNormCoefficient is the paper order family. -/
theorem rootNormCoefficient_eq_paperOrder_of_gap
    (h : S736PaperOrderGap (l := l) T b) :
    rootNormCoefficient (l := l) T b =
      fun _ => ((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) := by
  rw [rootNormCoefficient_eq_generatorSupply]
  funext i
  exact h

end LeanFormal.IUT.XiFPaper.S736RootNormCoefficientAuditActual

end
