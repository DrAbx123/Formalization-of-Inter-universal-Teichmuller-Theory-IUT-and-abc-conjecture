import tmp.sheaf.xif.PaperQPilotLogVolume

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Deep xi-f inequality attempt from actual q and Theta packet data

Task-561 write-only attempt.

Actual inputs:
* PaperQPilotLogVolume.lean: paperQPilotLogVolume C3 = localSignedLog C3.q,
  strictly negative for the actual contracting source q;
* FiniteThetaPacket C3.thetaPacket: the actual finite theta packet with
  scale j = realThetaValue q j and logVolume = sum of log scales;
* the actual procession normalization is packetLogVolume / card(label).

Actual packet signed hull candidate used here:
  actualSignedHullLogVolume C3 :=
    - C3.thetaPacket.logVolume / card(SignedLabel l).

This is the literal negative of the actual packet/procession log-volume per
label. It is not the value-layer sourceThetaHullLogVolume sSup.

Proved:
* the actual q-pilot signed log-volume is negative;
* if the actual theta packet is contracting (thetaPacket.q <= 1), then the
  theta packet log-volume is nonpositive, hence the actual signed hull
  candidate is nonnegative;
* consequently the actual xi-f inequality
  paperQPilotLogVolume C3 <= actualSignedHullLogVolume C3
  follows from the actual q contraction and the theta packet contraction.

Exact missing primitive:
thetaPacket.q <= 1 (equivalently thetaPacket.logVolume <= 0). The C3 field
thetaPacket is independent of C3.q in SourcePilotRegionData; no production
theorem identifies thetaPacket.q with the actual q norm or proves it is <= 1.
Without this theta-packet contraction the sign of the packet signed hull is
not determined.

No fake real, shortcut, True, PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.XiFInequalityProof3

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual finite label cardinality of the theta packet. -/
abbrev thetaCard : Nat := Fintype.card (SignedLabel l.value)

/-- Positivity of the actual theta label cardinality. -/
theorem thetaCard_pos : 0 < thetaCard (l := l) :=
  Fintype.card_pos_iff.mpr ⟨SignedLabel.representative l (0 : Fl l.value)⟩

/-- The actual packet/procession signed hull log-volume candidate. -/
def actualSignedHullLogVolume : Real :=
  -(C3.thetaPacket.logVolume) / (thetaCard (l := l) : Real)

/-- The actual theta packet signed hull is the negative packet log-volume per
label. -/
theorem actualSignedHullLogVolume_eq :
    actualSignedHullLogVolume C3 =
      -(C3.thetaPacket.logVolume) / (thetaCard (l := l) : Real) := rfl

/-- The actual q-pilot signed log-volume equals the actual completion
log-norm. -/
theorem qPilotLogVolume_eq_log_norm :
    paperQPilotLogVolume C3 = Real.log ‖C3.q.q‖ :=
  paperQPilotLogVolume_eq_log_norm C3

/-- The actual q-pilot signed log-volume is negative. -/
theorem qPilotLogVolume_neg : paperQPilotLogVolume C3 < 0 :=
  paperQPilotLogVolume_neg C3

/-- The actual q-pilot signed log-volume is the negative local log magnitude. -/
theorem qPilotLogVolume_eq_neg_magnitude :
    paperQPilotLogVolume C3 = -localLogMagnitude C3.q :=
  paperQPilotLogVolume_eq_neg_magnitude C3

/-- The actual theta packet log-volume is nonpositive under theta packet
contraction. -/
theorem thetaPacket_logVolume_nonpos
    (hq : C3.thetaPacket.q <= 1) :
    C3.thetaPacket.logVolume <= 0 := by
  unfold FiniteThetaPacket.logVolume
  apply Finset.sum_nonpos
  intro j hj
  rw [C3.thetaPacket.log_scale j]
  have hlog : Real.log C3.thetaPacket.q <= 0 :=
    Real.log_nonpos (le_of_lt C3.thetaPacket.q_pos) hq
  exact mul_nonpos_of_nonneg_of_nonpos
    (Nat.cast_nonneg (gaussExponent j.1).toNat) hlog

/-- Under theta packet contraction, the actual packet signed hull is
nonnegative. -/
theorem actualSignedHullLogVolume_nonneg
    (hq : C3.thetaPacket.q <= 1) :
    0 <= actualSignedHullLogVolume C3 := by
  have hlog := thetaPacket_logVolume_nonpos C3 hq
  have hcard : (0 : Real) < (thetaCard (l := l) : Real) := by
    exact_mod_cast thetaCard_pos (l := l)
  unfold actualSignedHullLogVolume
  have hnum : 0 <= -(C3.thetaPacket.logVolume) := neg_nonneg.mpr hlog
  exact div_nonneg hnum (le_of_lt hcard)

/-- Actual xi-f inequality from the actual q contraction and the theta packet
contraction. -/
theorem xi_f_inequality_of_theta_packet_contraction
    (hq : C3.thetaPacket.q <= 1) :
    paperQPilotLogVolume C3 <= actualSignedHullLogVolume C3 :=
  le_trans (le_of_lt (qPilotLogVolume_neg C3))
    (actualSignedHullLogVolume_nonneg C3 hq)

/-- Exact scalar form: the inequality is equivalent to the actual packet
average being at most the q-pilot magnitude. -/
theorem xi_f_inequality_iff_scalar
    (hcard : (0 : Real) < (thetaCard (l := l) : Real)) :
    paperQPilotLogVolume C3 <= actualSignedHullLogVolume C3 ↔
      C3.thetaPacket.logVolume / (thetaCard (l := l) : Real) <=
        -paperQPilotLogVolume C3 := by
  unfold actualSignedHullLogVolume
  constructor
  · intro h
    have h' : paperQPilotLogVolume C3 <= -(C3.thetaPacket.logVolume /
        (thetaCard (l := l) : Real)) := by
      simpa [neg_div] using h
    linarith
  · intro h
    have h' : paperQPilotLogVolume C3 <= -(C3.thetaPacket.logVolume /
        (thetaCard (l := l) : Real)) := by
      linarith
    simpa [neg_div] using h'

/-- The exact missing theta-packet contraction primitive. -/
def ThetaPacketContraction : Prop :=
  C3.thetaPacket.q <= 1

/-- The exact missing scalar comparison primitive, equivalent to the inequality
under the actual packet normalization. -/
def PacketAverageLeQMagnitude : Prop :=
  C3.thetaPacket.logVolume / (thetaCard (l := l) : Real) <=
    -paperQPilotLogVolume C3

/-- The theta packet contraction implies the scalar comparison. -/
theorem packetAverageLeQMagnitude_of_theta_packet_contraction
    (hq : C3.thetaPacket.q <= 1) :
    PacketAverageLeQMagnitude C3 := by
  have hlog := thetaPacket_logVolume_nonpos C3 hq
  have hcard : (0 : Real) < (thetaCard (l := l) : Real) := by
    exact_mod_cast thetaCard_pos (l := l)
  have hdiv : C3.thetaPacket.logVolume / (thetaCard (l := l) : Real) <= 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hcard)
  have hqneg : 0 < -paperQPilotLogVolume C3 := neg_pos.mpr (qPilotLogVolume_neg C3)
  exact le_trans hdiv (le_of_lt hqneg)

/-- The actual field-level status: q log negative, and the packet signed hull
sign is exactly controlled by the missing theta packet contraction. -/
theorem xi_f_inequality_status
    (hq : C3.thetaPacket.q <= 1) :
    (paperQPilotLogVolume C3 < 0) ∧
      (0 <= actualSignedHullLogVolume C3) ∧
      (paperQPilotLogVolume C3 <= actualSignedHullLogVolume C3) :=
  ⟨qPilotLogVolume_neg C3,
    actualSignedHullLogVolume_nonneg C3 hq,
    xi_f_inequality_of_theta_packet_contraction C3 hq⟩

end LeanFormal.IUT.N8Closure.XiFInequalityProof3

end
