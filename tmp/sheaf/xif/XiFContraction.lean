import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import Mathlib.Tactic

/-!
# Xi-f contraction: status of the q-contraction

The base file SourceXiFConstruction.lean assumes

    (I.theaterAt 0 0).thetaPacket.q <= 1.

This file determines what can be proved from the actual source declarations:

* the exact equivalence between q <= 1 and nonpositivity of every theta-pilot
  image log-degree (from CardHullRealGeneratorNonpositivity);
* a genuine sufficient source bridge: equality of the theater q with one of the
  initial Definition 3.1 reduction q-parameters, which are contracting by the
  actual SourceDefinition31Data field;
* the value-layer counterexample for q > 1: R9/hull bound fails.

No source declaration connects the initial reduction qParameter to the
theater theta-packet q. OriginalInput contains only the arithmetic alignment
and the family/link data; neither forces q <= 1. Therefore q <= 1 is an exact
source condition, not a theorem of OriginalInput. No axiom, sorry, toy field
or placeholder is used here.
-/

/-
VALUE-LAYER / CONDITIONAL SURROGATE - NOT PAPER-LEVEL XI-F.

This file is the task-490 value-layer contraction module. It does not formalize
or claim any of the following paper-level objects:

* the q-pilot object at (1,0); the q-pilot here is
  sourceThetaPilotPoint v R n oneSignedLabel, i.e. the theta-pilot point at the
  signed label 1;
* the paper q-pilot log-volume -|log q|; sourceQPilotLogVolume is
  card(SourceVolumeIndex l) * Real.log q (861 * log q at l = 41);
* the paper 1,circ U holomorphic-hull log-volume; sourceThetaHullLogVolume is
  sSup of pointwise sourceLocalLogDegree over sourceHolomorphicHull;
* the paper xi-f inclusion; hScaling is a substantive hypothesis of the base
  value-layer file.

The q-contraction q <= 1 is not derived from OriginalInput here. The file proves
the exact equivalence with image nonpositivity, the explicit source bridge
SourceQContractionBridge that would imply q < 1, and the value-layer
counterexample for q > 1. No target_accepted and no paper-level xi-f claim is
made. New paper-level tasks must not substitute this value-layer surrogate.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The exact source bridge that would connect the theater q to the Definition
3.1 reduction q-parameter. This is a named source condition, not a theorem of
OriginalInput. -/
def SourceQContractionBridge : Prop :=
  exists b : I.initial.badPlaces,
    (I.theaterAt 0 0).thetaPacket.q = I.initial.reduction.qParameter b

/-- If the theater q is one of the Definition 3.1 bad-place reduction
q-parameters, then it is strictly less than 1, using the actual
qParameter_contracting field. -/
theorem q_lt_one_of_sourceQContractionBridge
    (h : I.SourceQContractionBridge) :
    (I.theaterAt 0 0).thetaPacket.q < 1 := by
  rcases h with ⟨b, hb⟩
  rw [hb]
  have hqpos : 0 < I.initial.reduction.qParameter b := by
    rw [← hb]
    exact (I.theaterAt 0 0).thetaPacket.q_pos
  have hnorm : ‖I.initial.reduction.qParameter b‖ < 1 :=
    I.initial.q_parameter_contracting b
  rwa [Real.norm_eq_abs, abs_of_pos hqpos] at hnorm

/-- The named source bridge gives the contraction assumed by the base xi-f file. -/
theorem q_le_one_of_sourceQContractionBridge
    (h : I.SourceQContractionBridge) :
    (I.theaterAt 0 0).thetaPacket.q <= 1 :=
  le_of_lt (I.q_lt_one_of_sourceQContractionBridge h)

/-- The exact source sign dichotomy: q <= 1 iff every theta-pilot image has
nonpositive local log-degree. This is the actual CardHull theorem, restated
for the base xi-f use. -/
theorem q_le_one_iff_imageLogDegree_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.theaterAt 0 0).thetaPacket.q <= 1 ↔
      forall j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0 :=
  (I.sourceImageLogDegree_nonpos_iff_q_le_one v R n).symm

/-- If q > 1, the value-layer hull bound fails: this is the actual source
counterexample to the R9/hull inequality, not a toy model. -/
theorem not_hullVolume_le_imageVolume_of_one_lt_q
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    ¬ (I.sourceHullVolume v R n <= I.sourceImageVolume v R n) :=
  I.not_sourceHullVolume_le_imageVolume_of_one_lt_q v R n hq

/-- Status summary: the only proved route to q <= 1 is the explicit source
q-parameter bridge, while q <= 1 is equivalent to image nonpositivity. -/
theorem qContraction_status
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.SourceQContractionBridge -> (I.theaterAt 0 0).thetaPacket.q <= 1) ∧
      ((I.theaterAt 0 0).thetaPacket.q <= 1 ↔
        forall j : SignedLabel l.value,
          I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0) :=
  ⟨I.q_le_one_of_sourceQContractionBridge,
    I.q_le_one_iff_imageLogDegree_nonpos v R n⟩

end OriginalInput
end Theorem311Source

end IUT
