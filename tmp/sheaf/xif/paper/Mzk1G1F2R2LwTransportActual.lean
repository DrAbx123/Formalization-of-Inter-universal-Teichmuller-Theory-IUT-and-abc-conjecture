/- R2 PIECE 4: L_w root volume transport to the F-side paper Theta readout.

Uses localRootLogVolume (LocalStepV) and urRootAlpha_mass/rootExtensionHaar; the scalar
volume is (1/(2l))*nu(badPlaceQRegion) = -(cP/(2l))log p, and paperThetaReadoutB is
definitionally the rootNormHull tensor volume.  No fake equality between different carriers.
-/
import tmp.sheaf.xif.paper.Mzk1G1F2R2LocalStepVActual
import tmp.sheaf.xif.paper.Mzk1G1R1IAlphaMassConnectorActual
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped BigOperators Pointwise
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwTransportActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LocalStepVActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R1IAlphaMassConnectorActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual
open LeanFormal.IUT.XiFPaper.Mzk1URBadPlaceActualMapActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.LocalFieldLogarithm
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock (T := T) (b := b))]
variable [BorelSpace (qVFamTensorBlock (T := T) (b := b))]

/-- L_w volume equals (1/(2l)) times the actual q-lattice region volume. -/
theorem lwTransport_volume_eq :
    localRootLogVolume (T := T) (b := b) =
      (1 / (2 * (l.value : Real))) *
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
          MeasureTheory.Measure.addHaar (badPlaceQRegion (T := T) (b := b)) := by
  rw [localRootLogVolume_eq, urRootQ_log_norm_order, badPlaceQRegion_nu]
  unfold badPlaceCoeff
  ring

/-- The same L_w volume in the paper C1 order form -(cP/(2l))log p. -/
theorem lwTransport_volume_eq_order :
    localRootLogVolume (T := T) (b := b) =
      -((1 / (2 * (l.value : Real))) *
        (localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
          Real.log (qVFamTensorP T b : Real))) := by
  exact localRootLogVolume_eq_order (T := T) (b := b)

/-- paperThetaReadoutB is definitionally the rootNormHull tensor volume. -/
theorem paperThetaReadoutB_eq_rootNormHull_volume :
    paperThetaReadoutB (l := l) T b =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar (rootNormHull (l := l) T b) := rfl

#print axioms lwTransport_volume_eq
#print axioms lwTransport_volume_eq_order
#print axioms paperThetaReadoutB_eq_rootNormHull_volume
end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwTransportActual