import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetFormulaActual

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

theorem globalThetaPacket_log_scale_consumer (j : SignedLabel l.value) :
    Real.log ((globalThetaPacket I A C C3).scale j) =
      (gaussExponent j.1).toNat * Real.log (globalThetaPacket I A C C3).q :=
  FiniteThetaPacket.log_scale (globalThetaPacket I A C C3) j

theorem globalThetaPositivePacket_log_det_eq_sum_log_scale :
    Real.log (packetDet (globalThetaPositivePacket I A C C3)) =
      ∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale j) := by
  rw [globalThetaPositivePacket_det_eq_prod, Real.log_prod]
  intro j _
  exact ne_of_gt ((globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_log_det_eq_gauss_mul_log_q :
    Real.log (packetDet (globalThetaPositivePacket I A C C3)) =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_log_det_eq_sum_log_scale]
  calc
    (∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale j)) =
        ∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real) *
            Real.log (globalThetaPacket I A C C3).q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [globalThetaPacket_log_scale_consumer I A C C3 j]
    _ = (∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
      rw [Finset.sum_mul]

#check globalThetaPositivePacket_log_det_eq_gauss_mul_log_q

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetFormulaActual

end