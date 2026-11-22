import tmp.sheaf.xif.paper.S702QPilotRegionNormCandidateActual
import tmp.sheaf.xif.paper.S697QPilotRegionCoefficientReductionActual
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
/-! # S708: first identification of the S702 candidate
Exact first identification: every x in the qPilot root-label region at j=1
(fractional lattice F(N) times O_hol) has norm at most p^(-N).  The region is
thetaTensorScaledRegion by definition; the missing tensor-lattice norm bound is
recorded exactly, not asserted.  No fake norm inequality. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S708QPilotRootLabelRegionNormActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.S687QPilotSourceNormBoundActual
open LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
open LeanFormal.IUT.XiFPaper.S697QPilotRegionCoefficientReductionActual
open LeanFormal.IUT.XiFPaper.S702QPilotRegionNormCandidateActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- First identification of S702: region at j=1 has norm at most p^(-N). -/
def S708FirstIdentification : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotRootLabelRegion T b (oneSignedLabel (l := l)) →
      ‖x‖ ≤ Real.rpow (qVFamTensorP T b : Real)
        (-((qVFamily T b).order : Real))
/-- The root-label region is exactly thetaTensorScaledRegion at its coefficient. -/
theorem qPilotRootLabelRegion_eq_thetaTensorScaledRegion :
    qPilotRootLabelRegion T b (oneSignedLabel (l := l)) =
      thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
        (tuple := qVFamTensorTuple)
        (qPilotRootLabelCoefficient T b (oneSignedLabel (l := l))) :=
  rfl
/-- The same statement as a scaled-region norm bound. -/
theorem s708FirstIdentification_iff_scaled :
    S708FirstIdentification (l := l) T b ↔
      ThetaScaledRegionNormLe (l := l) T b
        (qPilotRootLabelCoefficient T b (oneSignedLabel (l := l)))
        (Real.rpow (qVFamTensorP T b : Real)
          (-((qVFamily T b).order : Real))) := by
  unfold S708FirstIdentification ThetaScaledRegionNormLe
    qPilotRootLabelRegion
  rfl
/-- Exact minimal tensor-lattice norm input: the fractional-lattice product
region at c_root is contained in the p^(-N) ball. -/
def FractionalTensorRegionNormBound : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple)
      (qPilotRootLabelCoefficient T b (oneSignedLabel (l := l))) →
      ‖x‖ ≤ Real.rpow (qVFamTensorP T b : Real)
        (-((qVFamily T b).order : Real))
/-- The first identification is exactly the tensor-lattice region norm bound. -/
theorem s708FirstIdentification_iff_fractionalTensor :
    S708FirstIdentification (l := l) T b ↔
      FractionalTensorRegionNormBound (l := l) T b := by
  unfold S708FirstIdentification FractionalTensorRegionNormBound
    qPilotRootLabelRegion
  rfl
/-- Exact remaining goal, recorded without inhabitant. -/
def S708ExactGoal : Prop :=
  FractionalTensorRegionNormBound (l := l) T b
end LeanFormal.IUT.XiFPaper.S708QPilotRootLabelRegionNormActual
