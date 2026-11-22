import tmp.sheaf.xif.paper.Mzk1P3DictQHALFWeightOneSummaryActual
import Mathlib.Tactic

/-! # REGRESSION: weights=1 => QHALF (runnable theorem check) -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQHALFRegressionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQHALFWeightOneSummaryActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Regression target: weight one forces the q-half equality. -/
theorem regression_weights_one_QHALF
    (hweight : forall b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = 1) :
    GAP_PC_QHALF (l := l) T :=
  QHALF_weight_one_reduction T hweight

/-- Regression target: weight one identifies signed q with 2l qPacket. -/
theorem regression_weights_one_signedLogQ
    (hweight : forall b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = 1) :
    nativeSignedLogQ T =
      (2 * (l.value : Real)) *
        (qPacket (l := l) T).normalizedLogVolume :=
  signedLogQ_weight_one T hweight

#print axioms regression_weights_one_QHALF
#print axioms regression_weights_one_signedLogQ
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQHALFRegressionActual
end
