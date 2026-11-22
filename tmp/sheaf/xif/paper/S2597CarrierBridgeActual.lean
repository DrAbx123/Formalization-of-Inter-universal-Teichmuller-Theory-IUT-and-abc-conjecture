import tmp.sheaf.xif.paper.S2592ValueMapCandidateActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2592ValueMapCandidateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2597CarrierBridgeActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V} (R : I.SourceImageRealization v)
variable {T : SourceNativeInitialThetaData.{0} l} {b : Bad (nativePlaceSelection T)}

/-- Normalized constant point: divide the tensor norm log by the source index
cardinality so that the source log-degree is exactly the tensor norm log. -/
noncomputable def S2597Point (a n c : Nat) : I.ThetaPilotPoint v :=
  I.constantThetaPilotPoint v R
    (Multiplicative.ofAdd
      (Real.log ‖S2588PointMap T b a n c‖ /
        (Fintype.card (SourceVolumeIndex l) : Real)))

theorem S2597_sourceLocalLogDegree
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (a n c : Nat) :
    I.sourceLocalLogDegree v (S2597Point I R (T := T) (b := b) a n c) =
      Real.log ‖S2588PointMap T b a n c‖ := by
  unfold S2597Point
  rw [I.sourceLocalLogDegree_constant v R _ hdeg]
  have hN : (Fintype.card (SourceVolumeIndex l) : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (sourceVolumeIndex_card_pos (l := l)))
  field_simp [hN]

#check S2597Point
#check S2597_sourceLocalLogDegree
#print axioms S2597_sourceLocalLogDegree

end LeanFormal.IUT.XiFPaper.S2597CarrierBridgeActual
end