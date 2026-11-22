import tmp.sheaf.xif.paper.Mzk1P3DictQCoeffActual
import Mathlib.Tactic

/-! # GREEN: documented QHALF <= GAP-PC-WEIGHT reduction -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQHALFWeightOneSummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Published reduction: weight-one implies the q-half identification. -/
theorem QHALF_weight_one_reduction
    (hweight : forall b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = 1) :
    GAP_PC_QHALF (l := l) T :=
  GAP_PC_QHALF_of_weight_one T hweight

/-- Corollary: actual signed q equals 2l times the q packet reading under weight one. -/
theorem signedLogQ_weight_one
    (hweight : forall b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = 1) :
    nativeSignedLogQ T =
      (2 * (l.value : Real)) *
        (qPacket (l := l) T).normalizedLogVolume :=
  nativeSignedLogQ_eq_twoL_mul_qPacket_of_weight_one T hweight

#check QHALF_weight_one_reduction
#check signedLogQ_weight_one
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQHALFWeightOneSummaryActual
end
