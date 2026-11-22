import tmp.sheaf.xif.paper.S3115NativeSourcePilotRegionDonors
import tmp.sheaf.n8.closure.NativeC3

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S3115NativeSourcePilotRegionDonors
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3116BKBTInhabitantAttempt

variable (X : N8NativeInput fiveLabel)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Exact BK inhabitant target. -/
def S3116BKTarget : Prop :=
  Nonempty (S3115BK X)

/-- Exact BT inhabitant target. -/
def S3116BTTarget : Prop :=
  Nonempty (S3115BT X)

/-- BT from a tensor landing donor whose prime is the native C3 prime. -/
noncomputable def S3116BT
    (L : NativeTensorLandingDonor.{0, 0} X)
    (hLp : L.p = nativeC3Prime X) : S3115BT X where
  p := L.p
  hp := L.hp
  tensorIndex := L.tensorIndex
  tensorFintype := L.tensorFintype
  tensorPlaceIndex := L.tensorPlaceIndex
  tensorPlaces := L.tensorPlaces
  tensorTuple := L.tensorTuple
  tensorUnit := L.tensorUnit
  tensorLanding := L.tensorLanding
  tensorLanding_q := by
    simpa [nativeQActual, nativeQ] using L.tensorLanding_q (nativeQDonorActual X)

theorem S3116_bt_nonempty
    (L : NativeTensorLandingDonor.{0, 0} X) (hLp : L.p = nativeC3Prime X) :
    S3116BTTarget X :=
  ⟨S3116BT X L hLp⟩

#check S3116BKTarget
#check S3116BTTarget
#check S3116BT
#check S3116_bt_nonempty

end LeanFormal.IUT.XiFPaper.S3116BKBTInhabitantAttempt
end