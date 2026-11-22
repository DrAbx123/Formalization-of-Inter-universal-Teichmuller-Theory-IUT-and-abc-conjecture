import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

/-!
  # Supply-layer discharges for the Corollary 3.12 gap inputs (value realization)

  Companion of `ABCBridge/Bridge/Cor312ComparisonGapReduction.lean` (imported
  here, not modified) and of the StepXI unit-region/Haar layer
  (`IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierHaarData.lean`).  The
  companion file reduces the two named gap fields of
  `Cor312EpsilonArithmeticComparison` to five named inputs (`hunit`, `hsplit`,
  `hptfin`, `hweightvol`, `hpoint` of
  `cor312GapAssembly_epsilonComparisonOfReducedInputs`) and leaves them open at
  the abstract interface.  This module locates, for the value-realized carrier
  `I.sourceUnitRegionHaarInterface`, where each input is supplied.

  * `hsplit` is a theorem here: the value-realized set volume is a sup of point
    volumes (`sourceSetVolume` of `SourceImageHullVolume.lean`), and the sup over
    a union is subadditive (`cor312GapSupply_sourceSetVolume_union_le`), so the
    split input holds for the realized interface on every ABC triple
    (`cor312GapSupply_sourceInterface_hsplit`).  No field of
    `IQHullLogVolumeInterface` supplies subadditivity; the abstract-side
    conditionalization to a unit-region membership datum is in the companion
    file.
  * `hptfin` also holds for the realized interface: the singleton set volume is
    `ofReal` of a real log-degree (`cor312GapSupply_sourceSetVolume_singleton`),
    hence finite, so the scale-shifted point has finite log-volume
    (`cor312GapSupply_sourceInterface_hptfin`).
  * `hunit` must be supplied by the normalization-comparison layer: it reduces to
    `ofReal D.degreeBound <= sourceHullVolume + ofReal D0`
    (`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`), whose
    left side transfers the existing field
    `SourceUnitRegionHaarData.unitRegion_logDegree_le` through
    `sourceSetVolume_le_ofReal_of_logDegree_le`.  The comparison itself (the
    analogue of the paper's normalization of the log-shell against the theta-pilot
    hull bound in the proof of IUT III Corollary 3.12) is not available in the
    current StepXI layer and remains open.  The real-line calibration cannot
    supply it: its hull/unit data are degenerate strength-check artifacts, not
    the paper carrier.
  * `hweightvol` has no abstract supply (counterexample in the companion file);
    here it reduces to the point-level degree-weight dictionary
    `arithmeticWeight x <= sourceLocalLogDegree v (scaling * point)`
    (`cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`), with
    `sourceLocalLogDegree` the value-level log-degree of
    `SourceImageHullVolume.lean` (the role of the paper's log-degree at the value
    level; see that module's documentation).  This dictionary is the minimal
    concrete semantics the input needs; it is not proved here.
  * `hpoint` (the point-volume bound of gap 2) attaches through the dual
    dictionary `(point volume).toReal <= logHeight1`; no source-layer
    point-height dictionary exists in the StepXI tree yet, so this direction is
    recorded as a gap.  Its calibration form holds with equality in the
    companion file (`realLineHullData_singletonVolume_eq_logHeight`).  On the
    arithmetic side,
    `cor312GapSupply_sourceGap1_of_valuationBound_degreeDictionary` shows that
    for the realized carrier the full gap-1 shape follows from the valuation
    bound of `ABCHeightArithmeticWeightComparison.lean` (DSH-B) plus the
    degree-weight dictionary above.

  Honesty notes: `SourceUnitRegionHaarData` is additional named data of the
  StepXI layer, not a consequence of `OriginalInput`; the unconditional-form
  results below are conditional on that datum.  No gap field of
  `Cor312EpsilonArithmeticComparison` is filled, and the PARKED items of the
  companion file remain PARKED.  Declarations carry the `cor312GapSupply_`
  prefix so they cannot collide with future additions in the StepXI source
  namespace they reside in.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe ua uv upi umon ui

open scoped BigOperators

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

noncomputable section

/-- The value-realized set volume of a singleton is its point volume:
the sup-type definition of sourceSetVolume. -/
theorem cor312GapSupply_sourceSetVolume_singleton (v : V) (x : I.ThetaPilotPoint v) :
    I.sourceSetVolume v {x} = I.sourcePointVolume v x := by
  unfold sourceSetVolume
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun hy => ?_
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  · exact le_iSup_of_le x (le_iSup_of_le (Set.mem_singleton x) le_rfl)

/-- The value-realized set volume is subadditive over unions: the sup
over a union is dominated by the sup over the first part plus the sup over the
second part.  This is the structural input whose absence from the abstract
carrier is the field card of the split input; in the source realization it is a theorem,
not a field. -/
theorem cor312GapSupply_sourceSetVolume_union_le (v : V) (S T : Set (I.ThetaPilotPoint v)) :
    I.sourceSetVolume v (S ∪ T) ≤ I.sourceSetVolume v S + I.sourceSetVolume v T := by
  unfold sourceSetVolume
  refine iSup_le fun x => iSup_le fun hx => ?_
  rcases hx with hx | hx
  · have h1 : I.sourcePointVolume v x ≤ ⨆ y ∈ S, I.sourcePointVolume v y :=
      le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    have h2 : (⨆ y ∈ S, I.sourcePointVolume v y) ≤
        (⨆ y ∈ S, I.sourcePointVolume v y) + (⨆ y ∈ T, I.sourcePointVolume v y) := by
      have h := add_le_add (le_refl (⨆ y ∈ S, I.sourcePointVolume v y))
        (bot_le : (0 : ENNReal) ≤ ⨆ y ∈ T, I.sourcePointVolume v y)
      simpa only [bot_eq_zero, add_zero] using h
    exact le_trans h1 h2
  · have h1 : I.sourcePointVolume v x ≤ ⨆ y ∈ T, I.sourcePointVolume v y :=
      le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    have h2 : (⨆ y ∈ T, I.sourcePointVolume v y) ≤
        (⨆ y ∈ S, I.sourcePointVolume v y) + (⨆ y ∈ T, I.sourcePointVolume v y) := by
      have h := add_le_add (bot_le : (0 : ENNReal) ≤ ⨆ y ∈ S, I.sourcePointVolume v y)
        (le_refl (⨆ y ∈ T, I.sourcePointVolume v y))
      simpa only [bot_eq_zero, zero_add] using h
    exact le_trans h1 h2

/-- The gap-2 split input holds unconditionally for the
value-realized source interface: the region is the image of the union, which
splits as the scaled unit region plus the scaled point, and the set volume is
subadditive. -/
theorem cor312GapSupply_sourceInterface_hsplit (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D) p a b c) ≤
        (I.sourceUnitRegionHaarInterface v R n D).logVolume
            ((I.sourceUnitRegionHaarInterface v R n D).scaleShift ''
              (I.sourceUnitRegionHaarInterface v R n D).unitRegion) +
          (I.sourceUnitRegionHaarInterface v R n D).logVolume
            {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)} := by
  intro a b c _
  change I.sourceSetVolume v ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c})) ≤
    I.sourceSetVolume v ((fun x => D.scaling * x) '' D.unitRegion) +
      I.sourceSetVolume v {(fun x => D.scaling * x) (p a b c)}
  rw [show (fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c}) =
      (fun x => D.scaling * x) '' D.unitRegion ∪
        {(fun x => D.scaling * x) (p a b c)} from by
    rw [Set.image_union, Set.image_singleton]]
  exact I.cor312GapSupply_sourceSetVolume_union_le v _ _

/-- The point-finiteness input holds unconditionally for the
value-realized source interface: the singleton set volume is ofReal of a real
log-degree, hence finite. -/
theorem cor312GapSupply_sourceInterface_hptfin (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) (a b c : Nat) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
      {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)} < ⊤ := by
  change I.sourceSetVolume v {(fun x => D.scaling * x) (p a b c)} < ⊤
  rw [I.cor312GapSupply_sourceSetVolume_singleton v]
  exact ENNReal.ofReal_lt_top

/-- The unit-region normalization input of gap 2 follows from the named
comparison between the unit-region log-degree bound and the hull volume:
ofReal D.degreeBound <= sourceHullVolume + ofReal D0.  This is exactly the
normalization layer where the supply must live; the degree bound itself is the
existing field SourceUnitRegionHaarData.unitRegion_logDegree_le. -/
theorem cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hB : ENNReal.ofReal D.degreeBound ≤ I.sourceHullVolume v R n + ENNReal.ofReal D₀) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀ := by
  change I.sourceSetVolume v D.unitRegion ≤
    I.sourceHullVolume v R n + ENNReal.ofReal D₀
  exact le_trans (I.sourceSetVolume_le_ofReal_of_logDegree_le v D.unitRegion_logDegree_le) hB

/-- The gap-1 weight comparison holds for the value-realized
source interface as soon as the point-level degree-weight dictionary is supplied:
arithmeticWeight x <= sourceLocalLogDegree v (lambda * q(a,b,c)).  This locates
the minimal concrete semantics of hweightvol at the singleton point degree, via
the sup-type set volume; the region volume is finite here because it is bounded
by the unit-region and point volumes through subadditivity. -/
theorem cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (hdeg : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
            p a b c)).toReal := by
  intro a b c habc
  have h1 : ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
      I.sourcePointVolume v (D.scaling * p a b c) :=
    ENNReal.ofReal_le_ofReal (hdeg a b c habc)
  have h2 : I.sourcePointVolume v (D.scaling * p a b c) ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
          p a b c) := by
    change I.sourcePointVolume v (D.scaling * p a b c) ≤
      I.sourceSetVolume v ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c}))
    unfold sourceSetVolume
    exact le_iSup_of_le (D.scaling * p a b c)
      (le_iSup_of_le ⟨p a b c, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩ le_rfl)
  have hptdeg : I.sourceSetVolume v {p a b c} ≤
      ENNReal.ofReal (I.sourceLocalLogDegree v (p a b c)) :=
    le_of_eq (I.cor312GapSupply_sourceSetVolume_singleton v (p a b c))
  have hfin1 : I.sourceSetVolume v
      ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c})) < ⊤ := by
    rw [image_mul_eq_scaledRegionImage D.scaling (D.unitRegion ∪ {p a b c})]
    refine lt_of_le_of_lt (le_trans
      (I.sourceSetVolume_scaledRegionImage_le_of_nonpos_logDegree v
        D.scaling_logDegree_nonpos)
      (le_trans (I.cor312GapSupply_sourceSetVolume_union_le v _ _)
        (add_le_add
          (I.sourceSetVolume_le_ofReal_of_logDegree_le v D.unitRegion_logDegree_le)
          hptdeg)))
      (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  have hne : (I.sourceUnitRegionHaarInterface v R n D).logVolume
      (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
        p a b c) ≠ ⊤ := by
    change I.sourceSetVolume v
      ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c})) ≠ ⊤
    exact ne_of_lt hfin1
  have hmain : ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
          p a b c) :=
    le_trans h1 h2
  have hmain' := ENNReal.toReal_mono hne hmain
  rwa [ENNReal.toReal_ofReal (arithmeticWeight_nonneg _)] at hmain'

/-- **Gap-1 shape for the realized carrier from two named arithmetic inputs.**
Given the uniform valuation bound (as consumed by the H1 reduction of
`ABCHeightArithmeticWeightComparison.lean`, DSH-B) and the point-level
degree-weight dictionary of
`cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`, the full gap-1
shape of `Cor312EpsilonArithmeticComparison` holds at the value-realized carrier
with the point map `p`.  In this direction no height identity is needed: the H1
reduction consumes the dictionary through `arithmeticWeight`.  The remaining
source-side gap-1 input is exactly the degree dictionary. -/
theorem cor312GapSupply_sourceGap1_of_valuationBound_degreeDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (hdeg : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          ((I.sourceUnitRegionHaarInterface v R n D).logVolume
            (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
              p a b c)).toReal :=
  cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound
    (I.sourceUnitRegionHaarInterface v R n D) p heps hval
    (I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p hdeg)

/-- **Gap-1 shape for the realized carrier from the additive input (version-2
mirror).**  Same carrier, point datum, and degree-weight dictionary as
`cor312GapSupply_sourceGap1_of_valuationBound_degreeDictionary`, with the refuted
uniform valuation bound replaced by the approved additive input
`height ≤ (1 + ε) · weight + A` (contract `ABCHeightWeightAdditiveBoundV2`,
IUT IV Theorem A shape); the conclusion is the additive gap-1 shape with the
explicit constant `A`. -/
theorem cor312GapSupply_sourceGap1_of_additiveBound_degreeDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps A : ℝ} (heps : 0 ≤ eps)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hdeg : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          ((I.sourceUnitRegionHaarInterface v R n D).logVolume
            (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
              p a b c)).toReal + A :=
  cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound
    (I.sourceUnitRegionHaarInterface v R n D) p heps hadd
    (I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p hdeg)

end

end OriginalInput
end Theorem311Source

end LeanFormal.IUT
