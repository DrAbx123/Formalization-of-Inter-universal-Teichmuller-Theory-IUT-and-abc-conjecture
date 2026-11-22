import tmp.sheaf.xif.XiFScaling
import tmp.sheaf.xif.XiFContraction
import Mathlib.Tactic

/-!
# Xi-f B-level exact obstructions (value-layer carrier)

STATUS: value-layer/surrogate only. This file does NOT prove paper-level
xi-f and does NOT claim target_accepted.

It formalizes the three exact B-level findings:

1. `q <= 1` is a named source-bridge condition: the actual bridge
   `SourceQContractionBridge` implies `q <= 1`, and `q <= 1` is exactly
   image-side nonpositivity; `OriginalInput` alone supplies neither the
   bridge nor `q <= 1`.
2. The scaling condition `hScaling` is false under pointwise degree
   faithfulness (`not_valueLayerScalingCondition_of_degreeFaithful`), with an
   explicit counterexample in `sourceScalingUnits`.
3. The value-layer q-pilot scalar is `card(SourceVolumeIndex l) * log q`,
   not the paper signed q-pilot scalar `-log q`; therefore the value-layer
   surrogate cannot be identified with paper xi-f. The paper objects
   (q-pilot at (1,0), 1,circ U hull, determinant/O(-) comparison) are not
   constructed here.

No fake theorem, no uninterpreted declaration, no toy carrier. All propositions are proved from
the actual XiFScaling/XiFContraction lemmas and SourceXiFConstruction.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

open LeanFormal.IUT

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. q <= 1 is a named source condition -/

/-- The actual source bridge to the Definition3.1 reduction q-parameter.
This is a named condition, not a field or theorem of `OriginalInput`. -/
abbrev QContractionSourceBridge : Prop :=
  I.SourceQContractionBridge

/-- The named source bridge implies the q-contraction used by the base xi-f
file. This is the exact positive direction available in XiFContraction. -/
theorem q_le_one_of_qContractionSourceBridge
    (h : QContractionSourceBridge I) :
    (I.theaterAt 0 0).thetaPacket.q <= 1 :=
  I.q_le_one_of_sourceQContractionBridge h

/-- The named source bridge gives the strict contraction. -/
theorem q_lt_one_of_qContractionSourceBridge
    (h : QContractionSourceBridge I) :
    (I.theaterAt 0 0).thetaPacket.q < 1 :=
  I.q_lt_one_of_sourceQContractionBridge h

/-- The exact value-layer sign dichotomy: q <= 1 iff every theta-pilot image
has nonpositive source local log-degree. -/
theorem bLevel_q_le_one_iff_imageLogDegree_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.theaterAt 0 0).thetaPacket.q <= 1 ↔
      ∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0 :=
  I.q_le_one_iff_imageLogDegree_nonpos v R n

/-- If q > 1, the actual hull/image inequality fails. Hence q <= 1 is not a
harmless normalization: it is a substantive source condition. -/
theorem bLevel_not_hullVolume_le_imageVolume_of_one_lt_q
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    ¬ (I.sourceHullVolume v R n <= I.sourceImageVolume v R n) :=
  I.not_hullVolume_le_imageVolume_of_one_lt_q v R n hq

/-! ## 2. hScaling is false under pointwise degree faithfulness -/

/-- Under pointwise degree faithfulness, the paper scaling condition is
false. This is the actual countertheorem from XiFScaling. -/
theorem scalingCondition_false_of_degreeFaithful
    (v : V) (R : I.SourceImageRealization v)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ValueLayerScalingCondition I v :=
  not_valueLayerScalingCondition_of_degreeFaithful I v R hdeg

/-- Explicit counterexample: under degree faithfulness, a source scaling unit
has strictly positive log-degree. -/
theorem scalingCondition_counterexample_of_degreeFaithful
    (v : V) (R : I.SourceImageRealization v)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∃ s : I.ThetaPilotPoint v,
      s ∈ I.sourceScalingUnits v ∧ 0 < I.sourceLocalLogDegree v s :=
  valueLayerScalingCondition_counterexample_of_degreeFaithful I v R hdeg

/-- Therefore the base source xi-f inclusion cannot be made unconditional by
dropping hScaling: its hScaling hypothesis is refutable in the actual
degree-faithful regime. This theorem states the conditional form explicitly. -/
theorem sourceXiFInclusion_conditional
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1)
    (hscal : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s <= 0) :
    I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n :=
  I.sourceXiFInclusion v R n hq hscal

/-! ## 3. The value-layer q-pilot scalar is not the paper signed scalar -/

/-- The paper signed q-pilot scalar normalization used for the mismatch:
`-log q`. This is only the scalar formula; it does not construct the paper
q-pilot object at (1,0). -/
def paperQPilotSignedLogScalar (q : Real) : Real :=
  -Real.log q

/-- The actual value-layer q-pilot log-volume is `card * log q`, with
positive cardinality. If `log q != 0`, it is not the paper signed scalar
`-log q`. -/
theorem sourceQPilotLogVolume_ne_paperSignedLogScalar
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hlog : Real.log ((I.theaterAt 0 0).thetaPacket.q) ≠ 0) :
    I.sourceQPilotLogVolume v R n ≠
      paperQPilotSignedLogScalar ((I.theaterAt 0 0).thetaPacket.q) := by
  intro h
  have hraw := I.sourceQPilotLogVolume_eq_gauss v R n
  rw [hraw] at h
  unfold paperQPilotSignedLogScalar at h
  have hzero :
      ((Fintype.card (SourceVolumeIndex l) : Real) + 1) *
        Real.log ((I.theaterAt 0 0).thetaPacket.q) = 0 := by
    linarith
  have hcardpos : (0 : Real) <
      (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast (sourceVolumeIndex_card_pos l)
  have hcoef : ((Fintype.card (SourceVolumeIndex l) : Real) + 1) ≠ 0 := by
    linarith
  have hlogzero : Real.log ((I.theaterAt 0 0).thetaPacket.q) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hcoef
  exact hlog hlogzero

/-- The raw scalar mismatch persists: even the normalized value-layer scalar
is `log q`, not the paper `-log q`, unless a separate sign/root
normalization is supplied. (The normalized q value is not the paper object
either; this is a scalar-only statement.) -/
theorem normalizedQPilotLogVolume_ne_paperSignedLogScalar
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hlog : Real.log ((I.theaterAt 0 0).thetaPacket.q) ≠ 0) :
    I.sourceQPilotLogVolume v R n /
        (Fintype.card (SourceVolumeIndex l) : Real) ≠
      paperQPilotSignedLogScalar ((I.theaterAt 0 0).thetaPacket.q) := by
  intro h
  have hcardpos : (0 : Real) <
      (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast (sourceVolumeIndex_card_pos l)
  have hraw := I.sourceQPilotLogVolume_eq_gauss v R n
  rw [hraw] at h
  unfold paperQPilotSignedLogScalar at h
  have hx : Real.log ((I.theaterAt 0 0).thetaPacket.q) =
      -Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
    have hmul := congrArg
      (fun y : Real => y * (Fintype.card (SourceVolumeIndex l) : Real)) h
    field_simp [ne_of_gt hcardpos] at hmul
    linarith
  have htwo : (2 : Real) *
      Real.log ((I.theaterAt 0 0).thetaPacket.q) = 0 := by
    linarith
  have hzero : Real.log ((I.theaterAt 0 0).thetaPacket.q) = 0 := by
    nlinarith
  exact hlog hzero

/-! ## 4. Exact B-level conjunction -/

/-- The three B-level obstructions as one proved conjunction, under the
explicit bridge/faithfulness/nonzero-log inputs. This is a summary of exact
facts, not a claim of paper xi-f. -/
theorem bLevelExactObstructions
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hbridge : QContractionSourceBridge I)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hlog : Real.log ((I.theaterAt 0 0).thetaPacket.q) ≠ 0) :
    ((I.theaterAt 0 0).thetaPacket.q <= 1) ∧
    (¬ ValueLayerScalingCondition I v) ∧
    (∃ s : I.ThetaPilotPoint v,
      s ∈ I.sourceScalingUnits v ∧ 0 < I.sourceLocalLogDegree v s) ∧
    (I.sourceQPilotLogVolume v R n ≠
      paperQPilotSignedLogScalar ((I.theaterAt 0 0).thetaPacket.q)) :=
  ⟨q_le_one_of_qContractionSourceBridge I hbridge,
    scalingCondition_false_of_degreeFaithful I v R hdeg,
    scalingCondition_counterexample_of_degreeFaithful I v R hdeg,
    sourceQPilotLogVolume_ne_paperSignedLogScalar I v R n hlog⟩

end OriginalInput
end Theorem311Source

end IUT
