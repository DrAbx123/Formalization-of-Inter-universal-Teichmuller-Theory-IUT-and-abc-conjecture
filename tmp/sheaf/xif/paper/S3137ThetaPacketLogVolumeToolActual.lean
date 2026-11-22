import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-!
# TOOL: generic finite theta-packet log-volume toolkit

**Reusable mathematical tool, not a paper object.**  Owner: lattice.  Generic
closed form of the log-volume of an ARBITRARY finite theta packet
(`FiniteThetaPacket.logVolume = (∑_j gaussExponent(j)) * log q`) together with
the sign/normalization corollaries.  These are the generic packet facts that
the q-pilot / LGP / normalization streams need, previously available only in
ad-hoc special forms.

Consumers: lattice log-shell/LGP value-group and q-pilot readings; qpilot
theta/gaussian packets; mainline q/Theta normalization.  Source: IUT II, theta
special values (Remark 2.5.1, (i)); IUT III, Prop. 3.9, (i), p. 115.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.ThetaPacketLogVolumeToolActual

open LeanFormal.IUT

/-- **Generic tool: closed form of the finite theta-packet log-volume.**  For any
finite theta packet, the log-volume is the total Gaussian weight times `log q`. -/
theorem finiteThetaPacket_logVolume_eq_weight_mul_log
    {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    packet.logVolume =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) *
        Real.log packet.q := by
  unfold FiniteThetaPacket.logVolume
  rw [Finset.sum_congr rfl (fun j _ => packet.log_scale j)]
  rw [Finset.sum_mul]

/-- **Generic tool: the log-volume of the Gaussian packet `ofQ`.** -/
theorem finiteThetaPacket_logVolume_ofQ_eq
    {l : PrimeGeFive} (q : ℝ) (hq : 0 < q) :
    (FiniteThetaPacket.ofQ (l := l) q hq).logVolume =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) *
        Real.log q := by
  rw [finiteThetaPacket_logVolume_eq_weight_mul_log, FiniteThetaPacket.ofQ_q]

/-- **Generic tool: monotonicity of the packet log-volume in its `q`.**  If
`q ≤ 1` then the log-volume is nonpositive. -/
theorem finiteThetaPacket_logVolume_nonpos_of_q_le_one
    {l : PrimeGeFive} (packet : FiniteThetaPacket l) (hq : packet.q ≤ 1) :
    packet.logVolume ≤ 0 := by
  rw [finiteThetaPacket_logVolume_eq_weight_mul_log]
  have hlog : Real.log packet.q ≤ 0 := Real.log_nonpos packet.q_pos.le hq
  have hweight : 0 ≤ ∑ j : SignedLabel l.value,
      ((gaussExponent j.1).toNat : ℝ) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  exact mul_nonpos_of_nonneg_of_nonpos hweight hlog

/-- **Generic tool: strict negativity when `q < 1` and a positive weight exists.**
If the total Gaussian weight is positive (true for `PrimeGeFive` since the
label `1` has exponent `1`), then `q < 1` forces strictly negative log-volume. -/
theorem finiteThetaPacket_logVolume_neg_of_q_lt_one
    {l : PrimeGeFive} (packet : FiniteThetaPacket l) (hq : packet.q < 1)
    (hpos : 0 < ∑ j : SignedLabel l.value,
      ((gaussExponent j.1).toNat : ℝ)) :
    packet.logVolume < 0 := by
  rw [finiteThetaPacket_logVolume_eq_weight_mul_log]
  have hlog : Real.log packet.q < 0 :=
    Real.log_neg packet.q_pos hq
  exact mul_neg_of_pos_of_neg hpos hlog

end LeanFormal.IUT.XiFPaper.ThetaPacketLogVolumeToolActual
