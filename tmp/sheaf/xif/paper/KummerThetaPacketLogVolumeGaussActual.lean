import tmp.sheaf.xif.paper.KummerThetaPacketLogDetGaussActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogVolumeGaussActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_value :
    packetLogVolume (globalThetaPositivePacket I A C C3) =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_logVolume_eq_log_det,
    globalThetaPositivePacket_log_det_eq_gauss_mul_log_q_consumer]

theorem globalThetaPositivePacket_det_eq_exp_logVolume_value :
    packetDet (globalThetaPositivePacket I A C C3) =
      Real.exp (packetLogVolume (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_eq_exp_gauss]
  congr 1
  exact (globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_value I A C C3).symm

theorem globalThetaPositivePacket_logVolume_rescale_eq_gauss (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket c hc
      (globalThetaPositivePacket I A C C3)) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_logVolume_rescale,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_value]

theorem globalThetaPositivePacket_logVolume_rescale_comp_eq_gauss (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) *
        (Real.log c2 + Real.log c1) +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [packetLogVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale_eq_gauss]
  ring

theorem globalThetaPositivePacket_logVolume_rescale_inv_eq_gauss (c : Real)
    (hc : 0 < c) :
    packetLogVolume (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q := by
  rw [packetLogVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale_eq_gauss,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_value]
  have hlog : Real.log (1 / c) = -Real.log c := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

theorem globalThetaPositivePacket_logVolume_rescale_inv (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      packetLogVolume (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_logVolume_rescale_inv_eq_gauss,
    ← globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_value]

theorem globalThetaPositivePacket_logVolume_rescale_inv_eq_log_det (c : Real)
    (hc : 0 < c) :
    packetLogVolume (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      Real.log (packetDet (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_logVolume_rescale_inv,
    globalThetaPositivePacket_logVolume_eq_log_det]

theorem globalThetaPositivePacket_exp_logVolume_rescale_inv (c : Real)
    (hc : 0 < c) :
    Real.exp (packetLogVolume (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3)))) =
      packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_logVolume_rescale_inv_eq_log_det]
  exact Real.exp_log (by
    rw [globalThetaPositivePacket_det_eq_prod]
    exact Finset.prod_pos
      (fun j _ => (globalThetaPacket I A C C3).scale_pos j))

#check globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_value
#check globalThetaPositivePacket_det_eq_exp_logVolume_value

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogVolumeGaussActual

end