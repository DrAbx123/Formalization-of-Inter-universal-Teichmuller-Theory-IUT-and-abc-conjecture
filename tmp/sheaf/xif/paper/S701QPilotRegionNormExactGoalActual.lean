import tmp.sheaf.xif.paper.QVPilotClassicalRootContainmentActual
import tmp.sheaf.xif.paper.S668QPilotRootExtensionPerBActual
import tmp.sheaf.xif.paper.S671QPilotRadiusAuditActual

-- S701: unfold qPilotClassicalRegion = thetaTensorScaledRegion c_norm and
-- record its exact norm radius / pointwise image bound.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S701QPilotRegionNormExactGoalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact local norm radius of the classical qPilot scaled region: p^{-c_norm}. -/
noncomputable def qPilotRegionNormRadius : Real :=
  (qVFamTensorP T b : Real) ^ (-(qVFamTensorCoefficient T b))

theorem qPilotRegion_eq_scaledRegion :
    qPilotClassicalRegion T b =
      thetaTensorScaledRegion
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (qPilotClassicalCoefficient T b) := rfl

theorem qPilotClassicalCoefficient_eq :
    qPilotClassicalCoefficient T b =
      fun _ : qVFamTensorV => qVFamTensorCoefficient T b := rfl

theorem qPilotRegionNormRadius_eq :
    qPilotRegionNormRadius T b =
      (qVFamTensorP T b : Real) ^ (-(qVFamTensorCoefficient T b)) := rfl

/-- Exact pointwise norm goal for the scaled region itself. -/
def QPilotRegionNormExactGoal : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotClassicalRegion T b →
      ‖x‖ ≤ qPilotRegionNormRadius T b

/-- Exact image-radius goal used by the root comparison. -/
def QPilotImageNormRadiusGoal : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotClassicalRegion T b →
      ‖qPilotToRootExtension (l := l) T b x‖ ≤ (rootImageRadius T b : Real)

theorem qPilotImageNormRadiusGoal_iff_radiusBound :
    QPilotImageNormRadiusGoal (l := l) T b ↔
      QPilotRadiusBoundObstacle (l := l) T b (qPilotClassicalCoefficient T b) := by
  rfl

#check qPilotRegionNormRadius
#check QPilotRegionNormExactGoal
#check QPilotImageNormRadiusGoal

end LeanFormal.IUT.XiFPaper.S701QPilotRegionNormExactGoalActual

end