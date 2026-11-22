import tmp.sheaf.xif.paper.S697QPilotRegionCoefficientReductionActual
import tmp.sheaf.xif.paper.S702QPilotRegionNormCandidateActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S712RootLabelRegionNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S697QPilotRegionCoefficientReductionActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Candidate radius of the root-label region at j=1. -/
noncomputable def rootLabelRegionRadiusCandidate : Real :=
  Real.rpow (qVFamTensorP T b : Real)
    (-((qVFamily T b).order : Real) / (2 * (l.value : Real)))

/-- Exact lattice norm bound still needed for the scaled region. -/
def RootLabelRegionLatticeNormBound : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotRootLabelRegion T b (oneSignedLabel (l := l)) →
      ‖x‖ ≤ rootLabelRegionRadiusCandidate T b

/-- Exact root image radius lower bound still needed. -/
def RootImageRadiusLowerBound : Prop :=
  rootLabelRegionRadiusCandidate T b ≤ (rootImageRadius T b : Real)

/-- Conditional S697 goal from the two exact identifications. -/
theorem s697ExactGoal_of_bounds
    (hregion : RootLabelRegionLatticeNormBound T b)
    (hroot : RootImageRadiusLowerBound T b) :
    RootLabelRegionNormLeRootRadius (l := l) T b := by
  intro x hx
  exact le_trans (hregion x hx) hroot

/-- Exact remaining goal in S697 form. -/
def S712ExactGoal : Prop :=
  RootLabelRegionNormLeRootRadius (l := l) T b

end LeanFormal.IUT.XiFPaper.S712RootLabelRegionNormActual

end
