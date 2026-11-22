import tmp.sheaf.xif.paper.S771RootNormCarrierActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.S692QPilotRegionNormExactActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S784RootNormRegionsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S771RootNormCarrierActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)

/-- Transfer a tensor set to the root-norm carrier. -/
def rootNormSet (S : Set (qVFamTensorBlock T b)) : Set (RootNormQVBlock (T := T) b) :=
  {x | x.toBlock ∈ S}

/-- qPilot classical region on the root-norm carrier. -/
abbrev rootNormQPilotRegion : Set (RootNormQVBlock (T := T) b) :=
  rootNormSet (T := T) b
    (qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)

/-- Normalized qPilot region on the root-norm carrier. -/
abbrev rootNormQPilotNormRegion : Set (RootNormQVBlock (T := T) b) :=
  rootNormSet (T := T) b (qPilotNormRegion (l := l) T b)

/-- Root hull on the root-norm carrier. -/
abbrev rootNormHullCarrier : Set (RootNormQVBlock (T := T) b) :=
  rootNormSet (T := T) b (rootNormHull (l := l) T b)

/-- Theta tensor scaled region on the root-norm carrier. -/
abbrev rootNormThetaScaledRegion (c : qVFamTensorV → Real) :
    Set (RootNormQVBlock (T := T) b) :=
  rootNormSet (T := T) b
    (thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) c)

/-- Theta tensor hull on the root-norm carrier. -/
abbrev rootNormThetaHull (c : SignedLabel l.value → qVFamTensorV → Real) :
    Set (RootNormQVBlock (T := T) b) :=
  rootNormSet (T := T) b
    (thetaTensorHull (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) c)

/-- Norm on the new carrier is exactly the rootBase norm of the block map. -/
theorem rootNormCarrier_norm_eq
    (x : RootNormQVBlock (T := T) b) :
    ‖x‖ = ‖qVFamBlockLinearEquiv T b x.toBlock‖ := rfl

/-- Actual transfer of the qPilotNormRegion / rootNormHull containment. -/
theorem rootNormQPilotNormRegion_subset_rootNormHull :
    rootNormQPilotNormRegion (l := l) T b ⊆ rootNormHullCarrier (l := l) T b := by
  intro x hx
  exact qPilotNormRegion_subset_rootNormHull (l := l) T b hx

/-- Exact root-norm bound condition for the qPilot region. -/
def RootNormQVPilotBound (R : Real) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotNormRegion (l := l) T b →
      ‖qVFamBlockLinearEquiv T b x‖ ≤ R

/-- Conditional norm bound on the new carrier. -/
theorem rootNormQPilot_norm_le
    {R : Real} (h : RootNormQVPilotBound (l := l) T b R)
    (x : RootNormQVBlock (T := T) b)
    (hx : x ∈ rootNormQPilotNormRegion (l := l) T b) :
    ‖x‖ ≤ R := by
  rw [rootNormCarrier_norm_eq]
  exact h x.toBlock hx

/-- Exact root-norm bound for the theta scaled region. -/
def RootNormThetaScaledBound (c : qVFamTensorV → Real) (R : Real) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) c →
      ‖qVFamBlockLinearEquiv T b x‖ ≤ R

theorem rootNormThetaScaled_norm_le
    {c : qVFamTensorV → Real} {R : Real}
    (h : RootNormThetaScaledBound (l := l) T b c R)
    (x : RootNormQVBlock (T := T) b)
    (hx : x ∈ rootNormThetaScaledRegion (l := l) T b c) :
    ‖x‖ ≤ R := by
  rw [rootNormCarrier_norm_eq]
  exact h x.toBlock hx

/-- Transferred theta scaled region is contained in the transferred theta hull. -/
theorem rootNormThetaScaled_subset_rootNormThetaHull
    {cfun : SignedLabel l.value → qVFamTensorV → Real}
    {c : qVFamTensorV → Real} {j : SignedLabel l.value}
    (hc : c = cfun j) :
    rootNormThetaScaledRegion (l := l) T b c ⊆
      rootNormThetaHull (l := l) T b cfun := by
  intro x hx
  rw [hc] at hx
  change x.toBlock ∈ thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
    (tuple := qVFamTensorTuple) (cfun j) at hx
  change x.toBlock ∈ thetaTensorHull (places := qVFamTensorPlaces T b)
    (tuple := qVFamTensorTuple) cfun
  exact subset_closure (Set.mem_iUnion.mpr ⟨j, hx⟩)

/-- The old tensor coordinate norm is unchanged; the new carrier is a
separate type with the rootBase norm. -/
def PaperFaithfulRootNormAudit : Prop :=
  (∀ x : RootNormQVBlock (T := T) b,
    ‖x‖ = ‖qVFamBlockLinearEquiv T b x.toBlock‖)

theorem paperFaithfulRootNormAudit :
    PaperFaithfulRootNormAudit T b := by
  unfold PaperFaithfulRootNormAudit
  intro x
  exact rootNormCarrier_norm_eq T b x

end LeanFormal.IUT.XiFPaper.S784RootNormRegionsActual

end
