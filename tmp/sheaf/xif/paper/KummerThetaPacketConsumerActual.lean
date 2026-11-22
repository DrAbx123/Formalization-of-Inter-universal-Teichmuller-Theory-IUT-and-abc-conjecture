import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual global Theta packet carried by the global Kummer/Ind data. -/
abbrev globalThetaPacket : FiniteThetaPacket l :=
  (globalKummerIndActionsData I A C C3).globalThetaPacket

theorem globalThetaPacket_eq (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    globalThetaPacket I A C C3 = C3.thetaPacket := rfl

theorem globalThetaPacket_q_pos :
    0 < (globalThetaPacket I A C C3).q := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.q_pos

theorem globalThetaPacket_scale_pos (j : SignedLabel l.value) :
    0 < (globalThetaPacket I A C C3).scale j := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.scale_pos j

theorem globalThetaPacket_scale_ne_zero (j : SignedLabel l.value) :
    (globalThetaPacket I A C C3).scale j ≠ 0 := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.scale_ne_zero j

theorem globalThetaPacket_scale_neg (j : SignedLabel l.value) :
    (globalThetaPacket I A C C3).scale (SignedLabel.neg j) =
      (globalThetaPacket I A C C3).scale j := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.scale_neg j

theorem globalThetaPacket_log_scale (j : SignedLabel l.value) :
    Real.log ((globalThetaPacket I A C C3).scale j) =
      (gaussExponent j.1).toNat * Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.log_scale j

theorem globalThetaPacket_logVolume_eq_sum :
    (globalThetaPacket I A C C3).logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale j) := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.logVolume_eq_sum

theorem globalThetaPacket_logVolume_neg_invariant :
    (∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale (SignedLabel.neg j))) =
      (globalThetaPacket I A C C3).logVolume := by
  rw [globalThetaPacket_eq]
  exact C3.thetaPacket.logVolume_neg_invariant

theorem globalKummerData_kummerArrow :
    (globalKummerIndActionsData I A C C3).kummerArrow =
      LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource.actualKummerArrow I 0 := rfl

theorem globalKummerData_kummerLayer :
    (globalKummerIndActionsData I A C C3).kummerLayer =
      LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource.actualVerticalKummerLayer I 0 := rfl

theorem globalKummerData_globalThetaPacket_eq :
    (globalKummerIndActionsData I A C C3).globalThetaPacket = C3.thetaPacket := rfl

theorem globalThetaPacket_logVolume_eq_gauss_mul_log_q :
    (globalThetaPacket I A C C3).logVolume =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPacket_logVolume_eq_sum]
  calc
    (∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale j)) =
        ∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real) *
            Real.log (globalThetaPacket I A C C3).q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [globalThetaPacket_log_scale]
    _ = (∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
      rw [Finset.sum_mul]

#check globalThetaPacket_logVolume_eq_sum
#check globalThetaPacket_logVolume_eq_gauss_mul_log_q
#check globalThetaPacket_log_scale

end LeanFormal.IUT.XiFPaper.KummerThetaPacketConsumerActual

end