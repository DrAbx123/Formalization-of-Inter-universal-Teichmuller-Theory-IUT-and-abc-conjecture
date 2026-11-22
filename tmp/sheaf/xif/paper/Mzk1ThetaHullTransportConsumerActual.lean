import tmp.sheaf.xif.paper.PaperThetaSideObjectActual

/-!
# Mzk1ThetaHullTransportConsumerActual — real consumer: theta-hull equality transport

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): combines the existing thetaSideObject hull equalities
into new transported equalities: thetaHolomorphicHullObject.carrier = singleScaledRegion,
image ⊆ singleScaledRegion, and hullLog/hullMeasure compatibility consequences. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaHullTransportConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootTensorThetaCarrierActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the theta-holomorphic hull carrier equals the single scaled region. -/
theorem thetaHolomorphicHullObject_carrier_eq_singleScaledRegion :
    (thetaHolomorphicHullObject T b).carrier = singleScaledRegion T b := by
  rw [← thetaSideObject_hull_eq_thetaHolomorphicHull T b,
    thetaSideObject_hull_eq_singleScaledRegion T b]

/-- Consumer: theta side image is contained in the single scaled region. -/
theorem thetaSideObject_image_subset_singleScaledRegion :
    (thetaSideObject T b).image ⊆ singleScaledRegion T b := by
  rw [← thetaSideObject_hull_eq_singleScaledRegion T b]
  exact (thetaSideObject T b).image_subset_hull

/-- Consumer: hull-log compatibility transported through the hull equality. -/
theorem thetaSideObject_hullLog_eq_thetaHolomorphicHullLog :
    (thetaSideObject T b).hullLog = (thetaHolomorphicHullObject T b).log :=
  (thetaSideObject T b).log_eq_thetaHolomorphicHull

/-- Consumer: hull-measure compatibility transported through the hull equality. -/
theorem thetaSideObject_hullMeasure_eq_thetaHolomorphicHullMeasure :
    (thetaSideObject T b).hullMeasure = (thetaHolomorphicHullObject T b).measure :=
  (thetaSideObject T b).measure_eq_thetaHolomorphicHull

end LeanFormal.IUT.XiFPaper.Mzk1ThetaHullTransportConsumerActual
end
