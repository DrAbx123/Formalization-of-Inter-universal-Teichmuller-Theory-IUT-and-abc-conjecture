import tmp.sheaf.xif.SourceXiFConstruction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractionWlogReduction

/-!
# Xi-f VALUE-LAYER scaling status (surrogate, NOT paper xi-f)

This file is explicitly a value-layer conditional surrogate. It is not a
formalization of paper-level xi-f and must not be substituted for the actual
q-pilot object or the signed 1,circ U hull volume. See task-491 audit.

Exact object/statement mismatches with paper-level xi-f:

1. sourceQPilotPoint is the theta-pilot point at signed label 1, not the actual
   (1,0) q-pilot object of the paper.
2. sourceQPilotLogVolume is sourceLocalLogDegree of that theta point. It equals
   card(SourceVolumeIndex l) * log q (at l = 41, 861 * log q), not the paper
   q-pilot log-volume -|log q|.
3. sourceThetaHullLogVolume is the supremum of pointwise source local
   log-degrees over the source holomorphic hull. It is not the paper's
   procession-normalized log-volume of the signed 1,circ U hull.
4. hScaling is the substantive ambient scaling/compactness condition
   (Remark 3.9.5, (i), (iii)); it is not a consequence of OriginalInput and is
   refutable under pointwise degree faithfulness.

The base SourceXiFConstruction.lean inclusion is therefore a value-layer
conditional surrogate, not paper xi-f. This file only determines the status of
the value-layer scaling hypothesis and records the exact paper condition and
the explicit degree-faithfulness counterexample.

Paper anchors: IUT III, Corollary 3.12, Step (xi) and Remark 3.9.5, (i), (iii);
corpus lines 7658-7750 (lambda * O hull and compactness) and 10354-10410
(1,circ U compactness/finiteness). The paper-level objects are not constructed
here.

No fake proof, no axiom, no toy structure, no target substitution. The exact
remaining value-layer hypothesis is ValueLayerScalingCondition (the paper's
ambient O-module/1,circ U compactness input), not a theorem of OriginalInput.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The exact paper-level scaling contraction needed by the base Xi-f
inclusion: every source hull scaling unit has nonpositive source log-degree.
This is the ambient lambda * O/compactness condition of Remark 3.9.5,
(i), (iii), not a formal consequence of OriginalInput. -/
def ValueLayerScalingCondition (v : V) : Prop :=
  forall s : I.ThetaPilotPoint v,
    s ∈ I.sourceScalingUnits v -> I.sourceLocalLogDegree v s <= 0

/-- Under q <= 1, the paper scaling condition is exactly the remaining half of
the R9 inequality sourceHullVolume <= sourceImageVolume; the image half is
the q-contraction. This is the sharp value-layer determination and shows that
hScaling is not derivable from q <= 1 alone. -/
theorem valueLayerScalingCondition_iff_hullVolume_le_imageVolume_of_q_le_one
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1) :
    ValueLayerScalingCondition I v ↔
      I.sourceHullVolume v R n <= I.sourceImageVolume v R n := by
  rw [I.sourceHullVolume_le_imageVolume_iff_q_le_one_and_scaling]
  constructor
  · intro hscal
    exact ⟨hq, hscal⟩
  · intro h
    exact h.2

/-- Under pointwise degree faithfulness, the paper scaling condition is false. -/
theorem not_valueLayerScalingCondition_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ValueLayerScalingCondition I v :=
  I.not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful v R hdeg

/-- Explicit counterexample to the paper scaling condition under pointwise
degree faithfulness: the constant theta-pilot point of exponent 1 is a source
scaling unit with positive log-degree card(SourceVolumeIndex l). -/
theorem valueLayerScalingCondition_counterexample_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∃ s : I.ThetaPilotPoint v,
      s ∈ I.sourceScalingUnits v ∧ 0 < I.sourceLocalLogDegree v s := by
  refine ⟨I.constantThetaPilotPoint v R (Multiplicative.ofAdd (1 : Real)),
    ?_, ?_⟩
  · exact I.constantThetaPilotPoint_mem_sourceScalingUnits v R
      (a := (1 : Real)) one_ne_zero hdeg
  · rw [I.sourceLocalLogDegree_constant v R 1 hdeg]
    simpa using (show (0 : Real) <
      (Fintype.card (SourceVolumeIndex l) : Real) by
      exact_mod_cast sourceVolumeIndex_card_pos l)

/-- The base Xi-f inclusion, with the scaling hypothesis named as the paper
condition. This is the exact consumer form of sourceXiFInclusion. -/
theorem sourceXiFInclusion_valueLayer_of_scalingCondition (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1)
    (hscal : ValueLayerScalingCondition I v) :
    I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n :=
  I.sourceXiFInclusion v R n hq hscal

/-- Status summary as a conjunction: the paper condition is exactly the
remaining scaling half under q <= 1, it is refutable under degree faithfulness,
and the base Xi-f inclusion consumes it as a named hypothesis. -/
theorem valueLayerScalingCondition_status (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1) :
    (ValueLayerScalingCondition I v ↔
        I.sourceHullVolume v R n <= I.sourceImageVolume v R n) ∧
      (ValueLayerScalingCondition I v ->
        I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n) := by
  constructor
  · exact I.valueLayerScalingCondition_iff_hullVolume_le_imageVolume_of_q_le_one
      v R n hq
  · intro hscal
    exact I.sourceXiFInclusion_valueLayer_of_scalingCondition v R n hq hscal

end OriginalInput
end Theorem311Source

end IUT