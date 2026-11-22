import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer :
    packetLogVolume (globalThetaPositivePacket I A C C3) =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_logVolume_eq_sum]
  calc
    (∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale j)) =
        ∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real) *
            Real.log (globalThetaPacket I A C C3).q := by
      apply Finset.sum_congr rfl
      intro j _
      exact FiniteThetaPacket.log_scale (globalThetaPacket I A C C3) j
    _ = (∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
      rw [Finset.sum_mul]

theorem globalThetaPositivePacket_det_pos_local_gauss :
    0 < packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_eq_prod]
  exact Finset.prod_pos
    (fun j _ => (globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_rescale_det_pos_local_gauss
    (c : Real) (hc : 0 < c) :
    0 < packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale]
  exact mul_pos (pow_pos hc _)
    (globalThetaPositivePacket_det_pos_local_gauss I A C C3)

theorem globalThetaPositivePacket_det_eq_exp_logVolume_local :
    packetDet (globalThetaPositivePacket I A C C3) =
      Real.exp (packetLogVolume (globalThetaPositivePacket I A C C3)) := by
  rw [← Real.exp_log
    (globalThetaPositivePacket_det_pos_local_gauss I A C C3)]
  congr 1
  exact (globalThetaPositivePacket_logVolume_eq_log_det I A C C3).symm

theorem globalThetaPositivePacket_rescale_det_eq_exp_logVolume_local
    (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      Real.exp (packetLogVolume
        (rescalePacket c hc (globalThetaPositivePacket I A C C3))) := by
  rw [← Real.exp_log
    (globalThetaPositivePacket_rescale_det_pos_local_gauss I A C C3 c hc)]
  congr 1
  exact (packetLogVolume_eq_log_det _).symm

theorem globalThetaPositivePacket_det_rescale_eq_exp_gauss (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      Real.exp ((Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_rescale_det_eq_exp_logVolume_local,
    globalThetaPositivePacket_logVolume_rescale,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer]

theorem globalThetaPositivePacket_det_eq_exp_gauss :
    packetDet (globalThetaPositivePacket I A C C3) =
      Real.exp ((∑ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_det_eq_exp_logVolume_local,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer]

theorem globalThetaPositivePacket_det_rescale_one_eq_exp_gauss :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (globalThetaPositivePacket I A C C3)) =
      Real.exp ((Fintype.card (SignedLabel l.value) : Real) * Real.log (1 : Real) +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_det_rescale_eq_exp_gauss]

#check globalThetaPositivePacket_det_rescale_eq_exp_gauss

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

end