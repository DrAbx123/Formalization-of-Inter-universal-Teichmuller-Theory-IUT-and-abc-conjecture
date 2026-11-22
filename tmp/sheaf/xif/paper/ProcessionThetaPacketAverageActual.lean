import tmp.sheaf.xif.paper.PaperThetaMagnitudeComparisonProof
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# Actual procession from the C3 theta packet and its average

This file constructs the canonical finite procession attached to the actual
C3 finite theta packet:

  c3ThetaProcession C3 : WeightedValues (SignedLabel l.value)
  value j = log(C3.thetaPacket.scale j)
  weight j = 1 / card(SignedLabel l.value)

It proves the actual average identity

  (c3ThetaProcession C3).average
    = C3.thetaPacket.logVolume / card(SignedLabel l.value).

It then reduces the paper relation ProcessionEqThetaPacketAverage to the exact
missing identification of the paper procession with this canonical packet
procession:

  P.procession = c3ThetaProcession C3.

Under that identification and the exact q identification
C3.thetaPacket.q = paperQParameter C3, the target
PaperThetaMagnitudeComparison C3 P follows from the theta-packet contraction
proved in PaperThetaMagnitudeComparisonProof.

No toy/identity axiom/sorry is used. c3ThetaProcession is the actual packet
log-scale procession; the paper P is not silently identified with it.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace ProcessionThetaPacketAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeComparisonProof
open LeanFormal.IUT.XiFPaper.XiFInequalityProof1
open scoped BigOperators

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- The actual finite theta label cardinality. -/
abbrev c3ThetaCard : Nat := Fintype.card (SignedLabel l.value)

theorem c3ThetaCard_pos : 0 < c3ThetaCard (l := l) :=
  Fintype.card_pos_iff.mpr
    ⟨SignedLabel.representative l (0 : Fl l.value)⟩

/-- The actual finite procession of the C3 theta packet: values are the actual
packet log-scales, weights are the uniform reciprocal cardinality. -/
noncomputable def c3ThetaProcession
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    WeightedValues (SignedLabel l.value) where
  value j := Real.log (C3.thetaPacket.scale j)
  weight _ := (c3ThetaCard (l := l) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (c3ThetaCard (l := l) : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (c3ThetaCard_pos (l := l)))
    exact (mul_inv_cancel₀ hcard).symm

/-- The canonical C3 packet procession has the literal packet average
logVolume / card. -/
theorem c3ThetaProcession_average
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    (c3ThetaProcession C3).average =
      C3.thetaPacket.logVolume / (c3ThetaCard (l := l) : Real) := by
  unfold WeightedValues.average c3ThetaProcession FiniteThetaPacket.logVolume
  rw [div_one, div_eq_mul_inv, mul_comm, Finset.mul_sum]

/-- The canonical packet procession weights are nonnegative. -/
theorem c3ThetaProcession_weights_nonnegative
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (j : SignedLabel l.value) :
    0 <= (c3ThetaProcession C3).weight j := by
  unfold c3ThetaProcession
  exact inv_nonneg.mpr (Nat.cast_nonneg (c3ThetaCard (l := l)))

/-- Under the exact q identification, the canonical packet procession average
is nonpositive. -/
theorem c3ThetaProcession_average_nonpos
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hQ : ThetaPacketQIdentification (l := l) C3) :
    (c3ThetaProcession C3).average <= 0 := by
  rw [c3ThetaProcession_average]
  have hlog := thetaPacket_logVolume_nonpos C3
    (thetaPacket_q_le_one_of_identification C3 hQ)
  have hcard : (0 : Real) < (c3ThetaCard (l := l) : Real) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  exact div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hcard)

/-- The actual packet average is exactly the canonical packet procession
average. -/
theorem actualThetaPacketAverage_eq_c3Procession_average
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    actualThetaPacketAverage (l := l) C3 =
      (c3ThetaProcession C3).average :=
  (c3ThetaProcession_average C3).symm

/-- If the paper procession is the canonical C3 packet procession, the exact
procession/packet average relation holds. -/
theorem processionEqThetaPacketAverage_of_procession_eq
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X (SignedLabel l.value))
    (h : P.procession = c3ThetaProcession C3) :
    ProcessionEqThetaPacketAverage (l := l) C3 P := by
  unfold ProcessionEqThetaPacketAverage actualThetaPacketAverage
  rw [h]
  exact c3ThetaProcession_average C3

/-- The target PaperThetaMagnitudeComparison follows from the exact
procession identification and the exact q identification. -/
theorem paperThetaMagnitudeComparison_of_procession_eq
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X (SignedLabel l.value))
    (hProc : P.procession = c3ThetaProcession C3)
    (hQ : ThetaPacketQIdentification (l := l) C3) :
    PaperThetaMagnitudeComparison C3 P :=
  paperThetaMagnitudeComparison_of_packet_alignment C3 P
    (processionEqThetaPacketAverage_of_procession_eq C3 P hProc) hQ

/-- Exact missing identification: the actual paper procession is the canonical
C3 theta-packet procession. This is the only remaining identification on the
procession side. -/
def PaperProcessionEqC3ThetaProcession
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X (SignedLabel l.value)) : Prop :=
  P.procession = c3ThetaProcession C3

/-- The paper relation from the exact procession identification. This is the
constructive direction; the converse is not asserted because equality of
averages does not recover a pointwise procession equality. -/
theorem processionEqThetaPacketAverage_of_paperProcessionEq
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperSignedHull X (SignedLabel l.value))
    (h : PaperProcessionEqC3ThetaProcession (l := l) C3 P) :
    ProcessionEqThetaPacketAverage (l := l) C3 P :=
  processionEqThetaPacketAverage_of_procession_eq C3 P h

end ProcessionThetaPacketAverageActual
end XiFPaper
end LeanFormal.IUT
end
