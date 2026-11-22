import tmp.sheaf.xif.paper.Mzk1WeightedDetPacketInstanceActual
import Mathlib.Tactic

/-! # GAP: actual q packet reading vs unweighted base-q total -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual q packet reading equals minus the unweighted base-q total / 2l. -/
theorem qPacket_normalized_eq_neg_baseQTotal_div :
    (qPacket (l := l) T).normalizedLogVolume =
      -baseQTotalLogMagnitude T / (2 * (l.value : Real)) := by
  rw [qPacket_normalized_eq_qActualBase]
  unfold qActualBaseNormalized
  rfl

#check qPacket_normalized_eq_neg_baseQTotal_div
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketActual
end
