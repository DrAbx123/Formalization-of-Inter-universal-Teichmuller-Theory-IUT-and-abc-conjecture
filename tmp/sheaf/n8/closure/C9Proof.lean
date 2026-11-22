import tmp.sheaf.n8.closure.C9Native
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealFinitePhaseGate
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractedSupplyRealization
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractionWlogReduction

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# C9 proof: reverse direction and exact no-go

The C9 targets are:
  MissingSourceQHullComparison : QSigned <= ThetaSigned
  MissingValuesBoundedByTheta : values <= ThetaSigned

The production source-signed-log file proves the REVERSE direction
`ThetaSigned <= QSigned` (hull contained in the image-union) and the
pointwise reverse `ThetaSigned <= -sourceLocalLogDegree` for image points.
Therefore the requested directions are not derivable from the current
donors.  This file proves the reverse theorems, and records the target
directions as conditional/obstruction theorems.  No placeholder tactic or uninterpreted declaration is used.  The exact obstruction is documented in
C9-NOSORRY-C9PROOF-20261025.md.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceValues
open LeanFormal.IUT.N8Closure.C9Native

namespace LeanFormal.IUT.N8Closure.C9Proof

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {Label : Type uL} [Group Label]
  (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- Reverse signed comparison: the production hull-containment theorem gives
`ThetaSigned <= QSigned`, not the C9 direction. -/
theorem thetaSigned_le_qSigned
    (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume D.place.v D.place.R n < ⊤) :
    ThetaSigned (D := D) n ≤ QSigned (D := D) n :=
  I.sourceSignedHullLogVolume_le_sourceSignedImageLogVolume
    D.place.v D.place.R n hfin

/-- Reverse value bound: every actual signed output value is at least Theta.
Proof: the image point lies in the source holomorphic hull, so its point
volume is at most the hull volume; taking negative real logs reverses the
inequality. -/
theorem thetaSigned_le_signed_value
    (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v)
    (hfin : I.sourceHullVolume D.place.v D.place.R n < ⊤)
    {z : ℝ} (hz : z ∈ Values (D := D) n x) :
    ThetaSigned (D := D) n ≤ z := by
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨c, rfl⟩
  let point := I.sourceThetaPilotPoint D.place.v D.place.R n c
  have hmem : point ∈ (I.sourceHolomorphicHull D.place.v D.place.R n :
      Set (I.ThetaPilotPoint D.place.v)) :=
    I.sourceThetaPilotPoint_mem_sourceHolomorphicHull D.place.v D.place.R n c
  have hle : I.sourcePointVolume D.place.v point ≤
      I.sourceHullVolume D.place.v D.place.R n := by
    unfold sourceHullVolume
    exact le_iSup_of_le point (le_iSup_of_le hmem le_rfl)
  have hof : ENNReal.ofReal (I.sourceLocalLogDegree D.place.v point) ≤
      I.sourceHullVolume D.place.v D.place.R n := by
    simpa [sourcePointVolume, point] using hle
  have hreal : I.sourceLocalLogDegree D.place.v point ≤
      (I.sourceHullVolume D.place.v D.place.R n).toReal := by
    by_cases hy0 : 0 ≤ I.sourceLocalLogDegree D.place.v point
    · have h := ENNReal.toReal_mono (ne_top_of_lt hfin) hof
      simpa [ENNReal.toReal_ofReal hy0] using h
    · have hnonneg : 0 ≤ (I.sourceHullVolume D.place.v D.place.R n).toReal :=
        ENNReal.toReal_nonneg
      linarith
  unfold ThetaSigned sourceSignedHullLogVolume sourceRealHullVolume
  rw [neg_le_neg_iff]
  exact hreal

/-- The C9 signed direction is exactly equivalent, under finiteness, to the
missing hull/image-volume comparison (the (xi-d) identity direction). -/
theorem qSigned_le_thetaSigned_iff_hullVolume_le_imageVolume
    (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume D.place.v D.place.R n < ⊤) :
    QSigned (D := D) n ≤ ThetaSigned (D := D) n ↔
      I.sourceHullVolume D.place.v D.place.R n ≤
        I.sourceSetVolume D.place.v (I.possibleThetaPilotImageSet D.place.v D.place.R n) :=
  I.sourceSignedImage_le_signedHull_iff_hullVolume_le_imageVolume
    D.place.v D.place.R n hfin

/-- The (xi-d) hull/image comparison is exactly the absence of a positive-degree
point in the source hull (finite phase). -/
theorem sourceHullVolumeLeImageObligation_iff_no_pos (n : ThetaPilotCarrier l) :
    (I.sourceHullVolume D.place.v D.place.R n ≤
        I.sourceSetVolume D.place.v
          (I.possibleThetaPilotImageSet D.place.v D.place.R n)) ↔
      ¬ ∃ z ∈ (I.sourceHolomorphicHull D.place.v D.place.R n :
          Set (I.ThetaPilotPoint D.place.v)),
        0 < I.sourceLocalLogDegree D.place.v z :=
  I.sourceHullVolume_le_imageVolume_iff_not_exists_pos_logDegree
    D.place.v D.place.R n

/-- Conditional form of the image-side nonpositive log-degree: the source
q-contraction is a hypothesis, not a theorem. -/
theorem sourceImageLogDegree_nonpos_of_q_lt_one
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q < 1) :
    ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree D.place.v
        (I.sourceThetaPilotPoint D.place.v D.place.R n j) ≤ 0 :=
  I.sourceImageLogDegree_nonpos_of_q_le_one D.place.v D.place.R n
    (le_of_lt hq)

/-- Conditional form of the hull nonpositivity: image nonpositivity and scaling
nonpositivity are explicit hypotheses. -/
theorem sourceNoPositiveHullDegree_of_contracted
    (n : ThetaPilotCarrier l)
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree D.place.v
        (I.sourceThetaPilotPoint D.place.v D.place.R n j) ≤ 0)
    (hscal : ∀ s ∈ I.sourceScalingUnits D.place.v,
      I.sourceLocalLogDegree D.place.v s ≤ 0) :
    ¬ ∃ z ∈ (I.sourceHolomorphicHull D.place.v D.place.R n :
        Set (I.ThetaPilotPoint D.place.v)),
      0 < I.sourceLocalLogDegree D.place.v z := by
  intro h
  rcases h with ⟨z, hz, hpos⟩
  exact not_le_of_gt hpos
    (I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators
      D.place.v D.place.R n himg hscal z hz)

/-- Conditional (xi-d) hull/image comparison from the two contraction
hypotheses.  No placeholder: the source conditions are explicit. -/
theorem sourceHullVolumeLeImageObligation_of_contracted
    (n : ThetaPilotCarrier l)
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree D.place.v
        (I.sourceThetaPilotPoint D.place.v D.place.R n j) ≤ 0)
    (hscal : ∀ s ∈ I.sourceScalingUnits D.place.v,
      I.sourceLocalLogDegree D.place.v s ≤ 0) :
    I.sourceHullVolume D.place.v D.place.R n ≤
      I.sourceSetVolume D.place.v
        (I.possibleThetaPilotImageSet D.place.v D.place.R n) :=
  (sourceHullVolumeLeImageObligation_iff_no_pos (D := D) n).mpr
    (sourceNoPositiveHullDegree_of_contracted (D := D) n himg hscal)

/-- Conditional (xi-d) comparison from q <= 1 and scaling nonpositivity. -/
theorem sourceHullVolumeLeImageObligation_of_q_le_one_and_scaling
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hscal : ∀ s ∈ I.sourceScalingUnits D.place.v,
      I.sourceLocalLogDegree D.place.v s ≤ 0) :
    I.sourceHullVolume D.place.v D.place.R n ≤
      I.sourceSetVolume D.place.v
        (I.possibleThetaPilotImageSet D.place.v D.place.R n) :=
  I.sourceHullVolume_le_imageVolume_of_q_le_one_and_scaling
    D.place.v D.place.R n hq hscal

/-- Exact obstruction: if q > 1, the target hull/image comparison is false. -/
theorem not_sourceHullVolumeLeImageObligation_of_one_lt_q
    (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    ¬ (I.sourceHullVolume D.place.v D.place.R n ≤
      I.sourceSetVolume D.place.v
        (I.possibleThetaPilotImageSet D.place.v D.place.R n)) := by
  intro h
  have h' : I.sourceHullVolume D.place.v D.place.R n ≤
      I.sourceImageVolume D.place.v D.place.R n := by
    unfold sourceImageVolume
    exact h
  exact (I.not_sourceHullVolume_le_imageVolume_of_one_lt_q
    D.place.v D.place.R n hq) h'

/-- Exact obstruction: if q > 1, a positive-degree point exists in the hull. -/
theorem exists_pos_sourceHullDegree_of_one_lt_q
    (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    ∃ z ∈ (I.sourceHolomorphicHull D.place.v D.place.R n :
        Set (I.ThetaPilotPoint D.place.v)),
      0 < I.sourceLocalLogDegree D.place.v z := by
  refine ⟨I.sourceThetaPilotPoint D.place.v D.place.R n
    (oneSignedLabel (l := l)), ?_, ?_⟩
  · exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull
      D.place.v D.place.R n (oneSignedLabel (l := l))
  · exact I.sourceImageLogDegree_pos_of_one_lt_q_of_ne_zero
      D.place.v D.place.R n (oneSignedLabel (l := l))
      oneSignedLabel_ne_zero hq

/-- Exact obstruction: the (xi-d) no-positive-hull-degree target fails when
q > 1. -/
theorem not_sourceNoPositiveHullDegree_of_one_lt_q
    (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    ¬ (¬ ∃ z ∈ (I.sourceHolomorphicHull D.place.v D.place.R n :
        Set (I.ThetaPilotPoint D.place.v)),
      0 < I.sourceLocalLogDegree D.place.v z) :=
  fun hno => hno (exists_pos_sourceHullDegree_of_one_lt_q (D := D) n hq)

/-- Exact obstruction: scaling nonpositivity is refuted under pointwise
degree faithfulness (source-level countertheorem). -/
theorem not_sourceScalingUnits_nonpos_of_degreeFaithful
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 D.place.v
        (D.place.R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ (∀ s ∈ I.sourceScalingUnits D.place.v,
      I.sourceLocalLogDegree D.place.v s ≤ 0) :=
  I.not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful
    D.place.v D.place.R hdeg

/-- Conditional C9 q/hull direction: only under a supplied comparison. -/
theorem missingSourceQHullComparison_of_hyp
    (h : MissingSourceQHullComparison (D := D)) :
    MissingSourceQHullComparison (D := D) :=
  h

/-- Exact obstruction: if q > 1 and the hull volume is finite, the C9 signed
q/hull direction is false. -/
theorem not_missingSourceQHullComparison_of_one_lt_q
    (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q)
    (hfin : I.sourceHullVolume D.place.v D.place.R n < ⊤) :
    ¬ (QSigned (D := D) n ≤ ThetaSigned (D := D) n) := by
  intro h
  have hle : I.sourceHullVolume D.place.v D.place.R n ≤
      I.sourceSetVolume D.place.v
        (I.possibleThetaPilotImageSet D.place.v D.place.R n) :=
    (qSigned_le_thetaSigned_iff_hullVolume_le_imageVolume (D := D) n hfin).mp h
  exact (not_sourceHullVolumeLeImageObligation_of_one_lt_q (D := D) n hq) hle

/-- Conditional C9 value-bound direction: only under a supplied bound. -/
theorem missingValuesBoundedByTheta_of_hyp
    (h : MissingValuesBoundedByTheta (D := D)) :
    MissingValuesBoundedByTheta (D := D) :=
  h

end LeanFormal.IUT.N8Closure.C9Proof

end
