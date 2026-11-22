import tmp.sheaf.xif.paper.Mzk1P3DictQPacketActual
import tmp.sheaf.xif.paper.Mzk1P3DictQCoeffActual
import Mathlib.Tactic

/-! # GREEN: actual signed q from qPacket (unweighted base-q total) -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketSignedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Signed q candidate read directly from the actual qPacket. -/
noncomputable def qPacketSignedLogQ : Real :=
  (2 * (l.value : Real)) * (qPacket (l := l) T).normalizedLogVolume

/-- qPacketSignedLogQ is minus the unweighted base-q total. -/
theorem qPacketSignedLogQ_eq_neg_baseQTotal :
    qPacketSignedLogQ (l := l) T = -baseQTotalLogMagnitude T := by
  unfold qPacketSignedLogQ
  rw [qPacket_normalized_eq_neg_baseQTotal_div (l := l) T]
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  field_simp [hl]

#check qPacketSignedLogQ
#check qPacketSignedLogQ_eq_neg_baseQTotal
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketSignedActual
end
