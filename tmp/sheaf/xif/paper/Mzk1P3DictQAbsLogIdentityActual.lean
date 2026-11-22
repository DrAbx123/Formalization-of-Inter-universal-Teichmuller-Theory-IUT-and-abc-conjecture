import tmp.sheaf.xif.paper.Mzk1P3DictQPacketSignedActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import Mathlib.Tactic

/-! # GREEN: paperQAbsLog(qPacketSignedLogQ) = qPacket.normalizedLogVolume -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQAbsLogIdentityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketSignedActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- paperQAbsLog of the signed qPacket log is exactly the q packet reading. -/
theorem paperQAbsLog_qPacketSignedLogQ :
    paperQAbsLog l (qPacketSignedLogQ (l := l) T) =
      (qPacket (l := l) T).normalizedLogVolume := by
  unfold paperQAbsLog qNormFactor qPacketSignedLogQ
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  field_simp [hl]

/-- Equivalent inverse 2l factor form. -/
theorem qPacketSignedLogQ_eq_twoL_mul_paperQAbsLog :
    qPacketSignedLogQ (l := l) T =
      (2 * (l.value : Real)) *
        paperQAbsLog l (qPacketSignedLogQ (l := l) T) := by
  rw [paperQAbsLog_qPacketSignedLogQ]
  unfold qPacketSignedLogQ
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  field_simp [hl]

#check paperQAbsLog_qPacketSignedLogQ
#check qPacketSignedLogQ_eq_twoL_mul_paperQAbsLog
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQAbsLogIdentityActual
end
