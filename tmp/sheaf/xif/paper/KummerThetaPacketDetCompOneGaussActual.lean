import tmp.sheaf.xif.paper.KummerThetaPacketRescaleCompEqActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleRpowPosActual
import tmp.sheaf.xif.paper.KummerThetaPacketLogDetGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompOneGaussActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompEqActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleRpowPosActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_comp_one_left_eq_exp_gauss
    (c2 : Real) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      Real.exp ((Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq,
    globalThetaPositivePacket_det_rescale_eq_exp_gauss]
  rw [mul_one]

theorem globalThetaPositivePacket_det_comp_one_right_eq_exp_gauss
    (c1 : Real) (hc1 : 0 < c1) :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      Real.exp ((Fintype.card (SignedLabel l.value) : Real) * Real.log c1 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq,
    globalThetaPositivePacket_det_rescale_eq_exp_gauss]
  rw [one_mul]

theorem globalThetaPositivePacket_det_comp_one_left_pos (c2 : Real) (hc2 : 0 < c2) :
    0 < packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) := by
  rw [globalThetaPositivePacket_det_comp_one_left_eq_exp_gauss]
  exact Real.exp_pos _

theorem globalThetaPositivePacket_det_comp_one_right_pos (c1 : Real) (hc1 : 0 < c1) :
    0 < packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) := by
  rw [globalThetaPositivePacket_det_comp_one_right_eq_exp_gauss]
  exact Real.exp_pos _

theorem globalThetaPositivePacket_det_comp_one_left_eq_rpow (c2 : Real) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      c2 ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq,
    globalThetaPositivePacket_det_rescale_eq_rpow_gauss_pos]
  simp

theorem globalThetaPositivePacket_det_comp_one_right_eq_rpow (c1 : Real) (hc1 : 0 < c1) :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      c1 ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq,
    globalThetaPositivePacket_det_rescale_eq_rpow_gauss_pos]
  simp

theorem globalThetaPositivePacket_det_comp_one_left_ne_zero (c2 : Real) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_comp_one_left_pos I A C C3 c2 hc2)

theorem globalThetaPositivePacket_det_comp_one_right_ne_zero (c1 : Real) (hc1 : 0 < c1) :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_comp_one_right_pos I A C C3 c1 hc1)

theorem globalThetaPositivePacket_log_det_comp_one_left (c2 : Real) (hc2 : 0 < c2) :
    Real.log (packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3)))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_det_comp_one_left_eq_exp_gauss, Real.log_exp]

theorem globalThetaPositivePacket_log_det_comp_one_right (c1 : Real) (hc1 : 0 < c1) :
    Real.log (packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3)))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c1 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_det_comp_one_right_eq_exp_gauss, Real.log_exp]

theorem globalThetaPositivePacket_logVolume_comp_one_left_gauss_local (c2 : Real)
    (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [packetLogVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer]
  simp

theorem globalThetaPositivePacket_logVolume_comp_one_right_gauss_local (c1 : Real)
    (hc1 : 0 < c1) :
    packetLogVolume (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c1 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [packetLogVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer]
  simp

theorem globalThetaPositivePacket_det_comp_one_left_eq_exp_logVolume (c2 : Real)
    (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      Real.exp (packetLogVolume (rescalePacket c2 hc2
        (rescalePacket (1 : Real) zero_lt_one
          (globalThetaPositivePacket I A C C3)))) := by
  rw [globalThetaPositivePacket_det_comp_one_left_eq_exp_gauss,
    globalThetaPositivePacket_logVolume_comp_one_left_gauss_local]

theorem globalThetaPositivePacket_det_comp_one_right_eq_exp_logVolume (c1 : Real)
    (hc1 : 0 < c1) :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      Real.exp (packetLogVolume (rescalePacket (1 : Real) zero_lt_one
        (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3)))) := by
  rw [globalThetaPositivePacket_det_comp_one_right_eq_exp_gauss,
    globalThetaPositivePacket_logVolume_comp_one_right_gauss_local]

theorem globalThetaPositivePacket_logVolume_comp_one_left_eq_log_det (c2 : Real)
    (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      Real.log (packetDet (rescalePacket c2 hc2
        (rescalePacket (1 : Real) zero_lt_one
          (globalThetaPositivePacket I A C C3)))) := by
  rw [globalThetaPositivePacket_logVolume_comp_one_left_gauss_local,
    globalThetaPositivePacket_log_det_comp_one_left]

theorem globalThetaPositivePacket_logVolume_comp_one_right_eq_log_det (c1 : Real)
    (hc1 : 0 < c1) :
    packetLogVolume (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      Real.log (packetDet (rescalePacket (1 : Real) zero_lt_one
        (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3)))) := by
  rw [globalThetaPositivePacket_logVolume_comp_one_right_gauss_local,
    globalThetaPositivePacket_log_det_comp_one_right]

#check globalThetaPositivePacket_det_comp_one_left_eq_exp_gauss
#check globalThetaPositivePacket_det_comp_one_right_eq_exp_gauss

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompOneGaussActual

end