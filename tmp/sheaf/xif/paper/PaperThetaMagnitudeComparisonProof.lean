import tmp.sheaf.xif.paper.XiFInequalityProof1
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # CONDITIONAL STATUS (xi-f)

Reduction only: PaperThetaMagnitudeComparison is reduced to ProcessionEqThetaPacketAverage and ThetaPacketQIdentification. Not an unconditional comparison.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Deep attempt: PaperThetaMagnitudeComparison from actual theta packet data

Target (from XiFInequalityProof1):

  PaperThetaMagnitudeComparison C3 P :=
    P.procession.average <= paperQPilotLogMagnitude C3
    (average <= |log(paperQParameter C3)|).

This file tries the actual theta-packet route:

* C3.thetaPacket : FiniteThetaPacket l, with
  logVolume = sum_j log(scale j) = sum_j (gaussExponent j) * log q;
* the packet average logVolume / card(SignedLabel l.value);
* the actual q-pilot q contraction paperQParameter C3 < 1;
* the actual q-pilot magnitude paperQPilotLogMagnitude C3 = |log q|.

Proved:
* if the theta packet q is the actual q-pilot norm, then it contracts:
  thetaPacket.q <= 1;
* hence every packet log-scale is nonpositive and the packet log-volume and
  its finite-cardinality average are nonpositive;
* the actual q-pilot magnitude is positive;
* therefore, if the paper procession average is the theta-packet average, the
  target PaperThetaMagnitudeComparison follows.

The exact missing source relations are recorded below. No toy/True/PUnit/
axiom/sorry is used; no inhabitant of the alignment is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace PaperThetaMagnitudeComparisonProof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.XiFInequalityProof1
open scoped BigOperators

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperSignedHull X label)

/-- The actual finite theta label cardinality. -/
abbrev thetaCard : Nat := Fintype.card (SignedLabel l.value)

/-- Positivity of the actual theta label cardinality. -/
theorem thetaCard_pos : 0 < thetaCard (l := l) :=
  Fintype.card_pos_iff.mpr
    ⟨SignedLabel.representative l (0 : Fl l.value)⟩

/-- The actual theta packet log-volume per finite label: the literal
finite-cardinality normalization of C3.thetaPacket.logVolume. -/
def actualThetaPacketAverage : Real :=
  C3.thetaPacket.logVolume / (thetaCard (l := l) : Real)

/-- Exact missing alignment: the paper procession average is the actual
C3 theta-packet finite average. This is not a field of PaperSignedHull and is
not a consequence of the C3.thetaPacket definition. -/
def ProcessionEqThetaPacketAverage : Prop :=
  P.procession.average = actualThetaPacketAverage (l := l) C3

/-- Exact missing q identification: the C3 theta packet q is the actual
q-pilot norm. -/
def ThetaPacketQIdentification : Prop :=
  C3.thetaPacket.q = paperQParameter C3

/-- The actual q-pilot norm is positive. -/
theorem paperQParameter_pos' : 0 < paperQParameter C3 :=
  paperQParameter_pos C3

/-- The actual q-pilot norm is less than one. -/
theorem paperQParameter_lt_one' : paperQParameter C3 < 1 := by
  unfold paperQParameter
  exact ArithmeticQPilotLogVolume.qNorm_lt_one C3.q

/-- The actual q-pilot magnitude |log q| is positive. -/
theorem paperQPilotLogMagnitude_pos : 0 < paperQPilotLogMagnitude C3 := by
  unfold paperQPilotLogMagnitude
  exact neg_pos.mpr (paperQPilotLogVolume_neg C3)

/-- Under the exact q identification, the C3 theta packet contracts. -/
theorem thetaPacket_q_le_one_of_identification
    (hq : ThetaPacketQIdentification (l := l) C3) :
    C3.thetaPacket.q <= 1 := by
  change C3.thetaPacket.q = paperQParameter C3 at hq
  rw [hq]
  exact le_of_lt (paperQParameter_lt_one' C3)

/-- Under theta-packet contraction, every log-scale is nonpositive. -/
theorem thetaPacket_log_scale_nonpos
    (hq : C3.thetaPacket.q <= 1) (j : SignedLabel l.value) :
    Real.log (C3.thetaPacket.scale j) <= 0 := by
  rw [C3.thetaPacket.log_scale j]
  have hlog : Real.log C3.thetaPacket.q <= 0 :=
    Real.log_nonpos (le_of_lt C3.thetaPacket.q_pos) hq
  exact mul_nonpos_of_nonneg_of_nonpos
    (Nat.cast_nonneg (gaussExponent j.1).toNat) hlog

/-- Under theta-packet contraction, the packet log-volume is nonpositive. -/
theorem thetaPacket_logVolume_nonpos
    (hq : C3.thetaPacket.q <= 1) :
    C3.thetaPacket.logVolume <= 0 := by
  unfold FiniteThetaPacket.logVolume
  apply Finset.sum_nonpos
  intro j hj
  exact thetaPacket_log_scale_nonpos C3 hq j

/-- Under theta-packet contraction, the finite packet average is nonpositive. -/
theorem actualThetaPacketAverage_nonpos
    (hq : C3.thetaPacket.q <= 1) :
    actualThetaPacketAverage (l := l) C3 <= 0 := by
  have hlog := thetaPacket_logVolume_nonpos C3 hq
  have hcard : (0 : Real) < (thetaCard (l := l) : Real) := by
    exact_mod_cast thetaCard_pos (l := l)
  unfold actualThetaPacketAverage
  exact div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hcard)

/-- The exact q identification makes the finite packet average nonpositive. -/
theorem actualThetaPacketAverage_nonpos_of_identification
    (hq : ThetaPacketQIdentification (l := l) C3) :
    actualThetaPacketAverage (l := l) C3 <= 0 :=
  actualThetaPacketAverage_nonpos C3
    (thetaPacket_q_le_one_of_identification C3 hq)

/-- Conditional proof of the target from the two exact source relations:
procession/packet alignment and theta-packet q identification. -/
theorem paperThetaMagnitudeComparison_of_packet_alignment
    (hAlign : ProcessionEqThetaPacketAverage (l := l) C3 P)
    (hQ : ThetaPacketQIdentification (l := l) C3) :
    PaperThetaMagnitudeComparison C3 P := by
  unfold PaperThetaMagnitudeComparison
  rw [hAlign]
  exact le_trans (actualThetaPacketAverage_nonpos_of_identification C3 hQ)
    (le_of_lt (paperQPilotLogMagnitude_pos C3))

/-- The same conditional theorem in terms of the actual procession bound
P.procession.average <= actualThetaPacketAverage C3, weaker than equality. -/
theorem paperThetaMagnitudeComparison_of_packet_bound
    (hBound : P.procession.average <= actualThetaPacketAverage (l := l) C3)
    (hQ : ThetaPacketQIdentification (l := l) C3) :
    PaperThetaMagnitudeComparison C3 P := by
  unfold PaperThetaMagnitudeComparison
  exact le_trans hBound
    (le_trans (actualThetaPacketAverage_nonpos_of_identification C3 hQ)
      (le_of_lt (paperQPilotLogMagnitude_pos C3)))

/-- Exact status: the two source relations are sufficient; neither is supplied
by the current C3/PaperSignedHull fields. -/
theorem paperThetaMagnitudeComparison_status
    (hAlign : ProcessionEqThetaPacketAverage (l := l) C3 P)
    (hQ : ThetaPacketQIdentification (l := l) C3) :
    (C3.thetaPacket.q <= 1) ∧
      (actualThetaPacketAverage (l := l) C3 <= 0) ∧
      PaperThetaMagnitudeComparison C3 P :=
  ⟨thetaPacket_q_le_one_of_identification C3 hQ,
    actualThetaPacketAverage_nonpos_of_identification C3 hQ,
    paperThetaMagnitudeComparison_of_packet_alignment C3 P hAlign hQ⟩

end PaperThetaMagnitudeComparisonProof
end XiFPaper
end LeanFormal.IUT
end
