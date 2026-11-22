import tmp.sheaf.xif.paper.S736RootNormCoefficientAuditActualAdapted
import tmp.sheaf.xif.paper.QVFamNormalizedRootRelationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S740SpectralCoefficientAuditActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S736RootNormCoefficientAuditActualAdapted

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The paper-faithful order coefficient. -/
noncomputable def paperOrderCoefficient : Real :=
  ((qVFamily T b).order : Real)

/-- The spectral supply coefficient. -/
noncomputable def spectralCoefficient : Real :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b

/-- Exact equality question: is the spectral coefficient the paper order? -/
def SpectralCoefficientEqualsOrder : Prop :=
  spectralCoefficient T b = paperOrderCoefficient T b

/-- Equivalent form of the S736 gap. -/
theorem spectralCoefficientEqualsOrder_iff_gap :
    SpectralCoefficientEqualsOrder T b ↔ S736PaperOrderGap T b := by
  unfold SpectralCoefficientEqualsOrder S736PaperOrderGap
    spectralCoefficient paperOrderCoefficient
  rfl

/-- If the spectral coefficient equals the paper order, then the S706 root
coefficient is the paper root coefficient. -/
theorem rootNormCoefficient_eq_paperOrder_of_spectral_eq
    (h : SpectralCoefficientEqualsOrder T b) :
    rootNormCoefficient T b = fun _ => paperOrderCoefficient T b := by
  rw [rootNormCoefficient_eq_generatorSupply]
  funext i
  exact h

/-- Conditional paper-faithfulness of the S706 rootHalfCoefficient family. -/
theorem rootHalfCoefficient_eq_paperOrderDiv_of_spectral_eq
    (h : SpectralCoefficientEqualsOrder T b) :
    rootHalfCoefficient (l := l) T b =
      fun _ => paperOrderCoefficient T b / (2 * (l.value : Real)) := by
  funext i
  unfold rootHalfCoefficient rootNormCoefficient
  rw [h]
  rfl

/-- Exact correction required for S706 paper-faithfulness. -/
def S740ExactCorrection : Prop :=
  ∀ b : Bad (nativePlaceSelection T), SpectralCoefficientEqualsOrder T b

end LeanFormal.IUT.XiFPaper.S740SpectralCoefficientAuditActualAdapted

end
