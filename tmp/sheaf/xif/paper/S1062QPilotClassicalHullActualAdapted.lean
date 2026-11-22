import tmp.sheaf.xif.paper.QVPilotClassicalRootContainmentActual
import tmp.sheaf.xif.paper.S900PerBThetaHullLogNonzeroActualAdapted
/-! # S1062: classical qPilot region is contained in the paper root theta hull
The paper qPilot is the classical F(c_norm)=order region; the theta hull is
the q[2u] root hull at cRoot=order/(2l).  We prove the classical region is
contained in the actual nonzero root theta hull. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1062QPilotClassicalHullActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S900PerBThetaHullLogNonzeroActualAdapted
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Root label region at j=1 equals the paper qPilotPaperRegion. -/
theorem qPilotRootLabelRegion_one_eq_qPilotPaperRegion :
    qPilotRootLabelRegion (l := l) T b (oneSignedLabel (l := l)) =
      qPilotPaperRegion (l := l) T b := by
  unfold qPilotRootLabelRegion qPilotPaperRegion thetaTensorScaledRegion
  congr 1
  funext i
  unfold qPilotRootLabelCoefficient qPilotRootCoefficient paperRootCoefficientFamily
    qVFamPaperRootCoefficient
  rw [oneSignedLabel_val_local, gaussExponent_one_toNat]
  norm_num
  ring
/-- Exact corrected containment: classical qPilot ⊆ nonzero root theta hull. -/
theorem qPilotClassicalRegion_subset_paperRootThetaHullNonzero :
    qPilotClassicalRegion T b ⊆ paperRootThetaHullNonzero (l := l) T b := by
  intro x hx
  have hx1 : x ∈ qPilotRootLabelRegion (l := l) T b
      (oneSignedLabel (l := l)) :=
    qPilotClassicalRegion_subset_rootLabelRegion_one T b hx
  rw [paperRootThetaHullNonzero_eq_qPilotPaperRegion (l := l) T b]
  rwa [qPilotRootLabelRegion_one_eq_qPilotPaperRegion (l := l) T b]
end LeanFormal.IUT.XiFPaper.S1062QPilotClassicalHullActualAdapted
