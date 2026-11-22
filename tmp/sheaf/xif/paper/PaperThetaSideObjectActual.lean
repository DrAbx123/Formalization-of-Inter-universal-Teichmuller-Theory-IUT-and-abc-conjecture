import tmp.sheaf.xif.paper.PaperRootTensorThetaCarrierActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual

-- S302: packaged final ThetaSideObject on qside rootTensorBlock, with actual
-- equality/compatibility to qside thetaHolomorphicHullObject/singleScaledRegion.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootTensorThetaCarrierActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

structure ThetaSideObject where
  image : Set (rootTensorBlock T b)
  image_eq : image = rootTensorThetaImageSetFinal T b
  indUnion : Set (rootTensorBlock T b)
  indUnion_eq : indUnion = rootTensorThetaIndUnion T b
  image_subset_indUnion : image ⊆ indUnion
  hull : Set (rootTensorBlock T b)
  hull_eq : hull = rootTensorFieldUnitLambdaOHull T b
  image_subset_hull : image ⊆ hull
  haar : Measure (rootTensorBlock T b)
  haar_eq : haar = rootTensorHaar T b
  hullMeasure : ENNReal
  hullMeasure_eq : hullMeasure = blockThetaScaledHullMeasure T b
  hullLog : Real
  hullLog_eq : hullLog = blockThetaScaledHullLog T b
  hull_ne_unitBall : hull ≠ (blockUnitBallPositive T b : Set (rootTensorBlock T b))
  isOUnitScalingClosed : IsOUnitScalingClosed T b hull
  hull_eq_singleScaledRegion : hull = singleScaledRegion T b
  hull_eq_thetaHolomorphicHull : hull = (thetaHolomorphicHullObject T b).carrier
  measure_eq_thetaHolomorphicHull : hullMeasure = (thetaHolomorphicHullObject T b).measure
  log_eq_thetaHolomorphicHull : hullLog = (thetaHolomorphicHullObject T b).log

noncomputable def thetaSideObject : ThetaSideObject T b where
  image := rootTensorThetaImageSetFinal T b
  image_eq := rfl
  indUnion := rootTensorThetaIndUnion T b
  indUnion_eq := rfl
  image_subset_indUnion := rootTensorThetaImage_subset_IndUnion T b
  hull := rootTensorFieldUnitLambdaOHull T b
  hull_eq := rfl
  image_subset_hull := rootTensorThetaImage_subset_scaledHull T b
  haar := rootTensorHaar T b
  haar_eq := rfl
  hullMeasure := blockThetaScaledHullMeasure T b
  hullMeasure_eq := rfl
  hullLog := blockThetaScaledHullLog T b
  hullLog_eq := rfl
  hull_ne_unitBall := by
    rw [rootTensorFieldUnitLambdaOHull, blockThetaScaledHull_eq_single]
    exact singleScaledRegion_ne_unitBall T b
  isOUnitScalingClosed := by
    rw [rootTensorFieldUnitLambdaOHull, blockThetaScaledHull_eq_single]
    exact singleScaledRegion_isOUnitScalingClosed T b
  hull_eq_singleScaledRegion := by
    rw [rootTensorFieldUnitLambdaOHull]
    exact blockThetaScaledHull_eq_single T b
  hull_eq_thetaHolomorphicHull := by
    rw [rootTensorFieldUnitLambdaOHull, blockThetaScaledHull_eq_single]
    rfl
  measure_eq_thetaHolomorphicHull := by
    change blockThetaScaledHullMeasure T b = singleScaledRegionMeasure T b
    exact blockThetaScaledHullMeasure_eq_single T b
  log_eq_thetaHolomorphicHull := by
    change blockThetaScaledHullLog T b = singleScaledRegionLog T b
    exact blockThetaScaledHullLog_eq_single T b

theorem thetaSideObject_hull_eq_thetaHolomorphicHull :
    (thetaSideObject T b).hull = (thetaHolomorphicHullObject T b).carrier :=
  (thetaSideObject T b).hull_eq_thetaHolomorphicHull

theorem thetaSideObject_hull_eq_singleScaledRegion :
    (thetaSideObject T b).hull = singleScaledRegion T b :=
  (thetaSideObject T b).hull_eq_singleScaledRegion

#check thetaSideObject
#check thetaSideObject_hull_eq_thetaHolomorphicHull
#check thetaSideObject_hull_eq_singleScaledRegion

end LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual

end