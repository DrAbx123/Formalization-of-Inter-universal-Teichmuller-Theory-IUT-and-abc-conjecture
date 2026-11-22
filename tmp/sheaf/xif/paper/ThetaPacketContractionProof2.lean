import tmp.sheaf.xif.PaperXiFInclusion
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import Mathlib.Tactic

/-!
# Second deep attempt: theta packet contraction

Task-571 attempts C3.thetaPacket.q <= 1 from:

* FiniteThetaPacket positivity and log-scale formulas;
* the q-pilot q norm < 1 (paperQParameter C3 < 1);
* source C3/Theta packet identification data.

The audit finds one exact missing source relation:

  C3.thetaPacket.q = paperQParameter C3

Without this relation, C3.thetaPacket is an independent FiniteThetaPacket
field.  FiniteThetaPacket permits arbitrary positive q; the positive q = 2
packet is an actual counterexample to q <= 1.  The q-pilot norm < 1 concerns
C3.q, not C3.thetaPacket.q.  Thus q <= 1 is not derivable from the available
data.

This file proves:
* the actual finite-packet counterexample q = 2 (not q <= 1);
* a conditional theorem: the exact identification with the q-pilot norm gives
  C3.thetaPacket.q <= 1;
* the exact missing relation as a named proposition.

No arbitrary inequality, True/PUnit/axiom/sorry is used.  WRITE-ONLY;
compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.ThetaPacketContractionProof2

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-! ## 1. Actual finite-packet counterexample -/

/-- The actual positive packet with q = 2. -/
noncomputable def packetQTwo : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (l := l) 2 (by norm_num)

@[simp] theorem packetQTwo_q : (packetQTwo (l := l)).q = 2 := rfl

/-- The actual q = 2 packet does not satisfy q <= 1. -/
theorem packetQTwo_not_contracted : ¬ (packetQTwo (l := l)).q <= 1 := by
  rw [packetQTwo_q]
  norm_num

/-- Therefore positivity/log-scale structure of FiniteThetaPacket alone does
not imply contraction. -/
theorem finiteThetaPacket_positivity_not_enough :
    ∃ P : FiniteThetaPacket l, ¬ P.q <= 1 :=
  ⟨packetQTwo (l := l), packetQTwo_not_contracted (l := l)⟩

/-! ## 2. Exact missing source relation -/

/-- The exact missing relation: the theta packet q is the actual q-pilot q
norm. -/
def ThetaPacketQIdentification : Prop :=
  C3.thetaPacket.q = paperQParameter C3

/-- The independent available q facts: the theta packet q is positive, while
the q-pilot norm is positive and less than one. -/
theorem available_q_facts :
    0 < C3.thetaPacket.q ∧ 0 < paperQParameter C3 ∧ paperQParameter C3 < 1 :=
  ⟨C3.thetaPacket.q_pos, paperQParameter_pos C3,
    (by
      unfold paperQParameter
      exact qNorm_lt_one C3.q)⟩

/-- The exact missing relation supplies the contraction. -/
theorem thetaPacket_q_le_one_of_identification
    (h : ThetaPacketQIdentification (C3 := C3)) :
    C3.thetaPacket.q <= 1 := by
  change C3.thetaPacket.q = paperQParameter C3 at h
  rw [h]
  exact le_of_lt (by
    unfold paperQParameter
    exact qNorm_lt_one C3.q)

/-- The missing relation restated as an equality of the actual q-pilot norm. -/
def MissingThetaPacketQIdentification : Prop :=
  ThetaPacketQIdentification (C3 := C3)

/-! ## 3. Why no other available identity suffices

FiniteThetaPacket gives q_pos and scale_eq/log_scale; the scales are powers of
q and do not force q <= 1 (the q = 2 packet above is actual).  The q-pilot norm
fact paperQParameter C3 < 1 concerns C3.q, a different field of C3.  No source
lemma identifies C3.thetaPacket.q with paperQParameter C3.  The exact missing
relation is therefore the identification above. -/

/-- The available q-pilot contraction does not mention the theta packet q. -/
theorem paperQParameter_lt_one' : paperQParameter C3 < 1 := by
  unfold paperQParameter
  exact qNorm_lt_one C3.q

/-- The theta packet q positivity is independent of the q-pilot norm sign
comparison; this is only a conjunction of the two available facts. -/
theorem thetaPacket_q_pos_and_qPilot_contracted :
    0 < C3.thetaPacket.q ∧ paperQParameter C3 < 1 :=
  ⟨C3.thetaPacket.q_pos, paperQParameter_lt_one' C3⟩

end LeanFormal.IUT.N8Closure.ThetaPacketContractionProof2
