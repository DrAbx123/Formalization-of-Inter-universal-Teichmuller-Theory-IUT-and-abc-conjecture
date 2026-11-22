import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalHeight
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryPrimeSupport

/-!
  # Dictionary layer for the two Corollary 3.12 gap inputs (weight / point-height)

  Companion of `ABCBridge/Bridge/Cor312ComparisonGapReduction.lean` and
  `ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean` (both imported, neither
  modified).  The supply layer reduced the gap inputs `hweightvol` and `hpoint`
  to two dictionaries at the value-realized carrier:

  * weight dictionary: `arithmeticWeight x <= sourceLocalLogDegree v (λ * q)`;
  * point-height dictionary: `(sourceSetVolume v {λ * q}).toReal <= logHeight₁ x`.

  This module determines the provability status of both dictionaries and lands
  the maximal provable fragments.

  ## Judgment table (item: verdict + grounds)

  1. Weight dictionary -- NOT provable as stated; PARKED, obstruction recorded.
     (a) The point map `p` is a free variable of the interface statements; the
         carrier `I.ThetaPilotPoint v` is the function type
         `ThetaPilotCarrier l × SignedLabel l.value → Mon v`
         (`SourceImageHull.lean:139`) and no declaration in the tree links it to
         arithmetic data.
     (b) `sourceLocalLogDegree` is the finite sum of `logDegreeAt`
         (`SourceImageHullVolume.lean:103`), and `logDegreeAt` is the genuine
         degree homomorphism of the source prime strip
         (`SourceImageHull.lean:100`), not `Real.log` of a number; the only
         realized degree facts are the `q`-instance field `degree_of_q` and the
         explicit faithfulness hypothesis (`hdeg`) used below.
     (c) Direction: by `cor312GapDict_weightDictionary_iff_scalingSeparated` the
         dictionary is equivalent to `weight <= logDegree λ + logDegree q`, and
         since the frozen scaling has nonpositive log-degree
         (`SourceUnitRegionHaarData.scaling_logDegree_nonpos`) the dictionary
         implies the scaling-free bound `weight <= logDegree q`
         (`cor312GapDict_weightDictionary_implies_scalingFree`): any proof must
         at least show that the point's own log-degree dominates the whole
         arithmetic weight `log (radical (a * b * c))`, strictly more than the
         scaling-free reading because `logDegree λ <= 0` subtracts slack.
     Maximal provable fragments landed:
     * `cor312GapDict_weightDictionary_iff_scalingSeparated`,
       `cor312GapDict_weightDictionary_implies_scalingFree` (exact shape);
     * `cor312GapDict_exists_pointMap_weightDictionary` (satisfiability: some
       point map satisfies the dictionary at the fixed scaling, under degree
       faithfulness on positive-real exponents);
     * `cor312GapDict_weightDictionary_not_universal` (counterexample: some
       point map violates it at any given ABC triple).

  2. Point-height dictionary -- NOT provable as stated; PARKED, reduced to an
     exact minimal real inequality, with counterexample.
     Through `cor312GapDict_singletonVolume_toReal_eq_max` the truncated volume
     `(vol {x}).toReal` is `max (logDegree x) 0`; hence for nonnegative height,
     `cor312GapDict_singletonVolume_toReal_le_iff` removes all `ENNReal`/`toReal`
     content: the dictionary is equivalent to the untruncated real inequality
     `logDegree (λ * q) <= logHeight₁ x`.
     The per-place route through the accepted atomic decomposition
     `abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport`
     (`ABCInvariantLocalHeight.lean:136`) is landed as
     `cor312GapDict_le_logHeight₁_of_le_localTerm`: a bound by ONE
     nonarchimedean local term suffices (the other terms of the sum are
     nonnegative, so the single term is dominated by the total).  The missing
     primitive is therefore the place-degree dictionary identifying one local
     height term with the realized log-degree of `λ * q`; no such identification
     exists for the free map `p`, so the dictionary is parked.
     Fragments: `cor312GapDict_exists_pointMap_pointHeightDictionary`
     (satisfiability) and `cor312GapDict_pointHeightDictionary_not_universal`
     (counterexample).

  3. Attachment to the frozen consumers (no frozen file modified):
     * `hpoint`: `cor312GapDict_sourcePointBound_of_degree_le_height` consumes
       the frozen `cor312Gap2_pointBound_of_singletonVolume_le_logHeight` with
       the minimal premise `logDegree (λ * p abc) <= logHeight₁ x` (plus the H1
       valuation bound), producing the `hpoint`-shape with `D₁ = 0` at the
       realized carrier; in the frozen gap-2 assembly this is the `hpoint` slot,
       and `hunit`/`hsplit`/`hptfin` are unchanged.
     * `hweightvol`: the frozen
       `cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary` consumes
       the weight dictionary as-is; its minimal premise is the single real
       inequality `weight <= logDegree (λ * q)` (no further minimization is
       possible on this side; the shape is already real-valued), and the frozen
       `cor312GapSupply_sourceGap1_of_valuationBound_degreeDictionary` then
       yields the gap-1 shape from it.

  Honesty notes: degree faithfulness (`hdeg`) used in the witnesses and
  counterexamples is an explicit hypothesis, matching the pattern of the frozen
  `sourceLocalLogDegree_constant` / `sourceLocalLogDegree_thetaPilotPoint`; it is
  NOT a field of `SourceImageRealization`, whose only degree field is the
  `q`-instance `degree_of_q`.  `SourceUnitRegionHaarData` remains additional
  named data, and no gap field of `Cor312EpsilonArithmeticComparison` is filled
  by this module.

  (Development record: batch E / e1; scratch evidence and judgment reasoning in
  `logs/coordination/cor312-gap-dictionaries-20261016.md`, compile exit 0.)
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe ua uv upi umon ui

/-- The logarithmic height of the actual ABC point is nonnegative. -/
theorem cor312GapDict_abcRationalPoint_logHeight₁_nonneg {a b c : Nat}
    (habc : IsABCTriple a b c) :
    0 ≤ Height.logHeight₁ (abcRationalPoint a c) := by
  rw [abcRationalPoint_logHeight₁ habc]
  refine Real.log_nonneg ?_
  have h1 : 1 ≤ c := by
    obtain ⟨ha, hb, hsum, _⟩ := habc
    omega
  exact_mod_cast h1

/-- If a real `t` is bounded by one nonarchimedean local term of the canonical
height of `abcRationalPoint a c` (a term of the accepted
`arithmeticPrimeSupport` decomposition, over which all other terms are
nonnegative), then `t` is bounded by the whole logarithmic height. -/
theorem cor312GapDict_le_logHeight₁_of_le_localTerm {a b c : Nat}
    (habc : IsABCTriple a b c) {t : ℝ}
    (h : ∃ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      t ≤ max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) * Real.log q) :
    t ≤ Height.logHeight₁ (abcRationalPoint a c) := by
  obtain ⟨q, hq, hle⟩ := h
  rw [abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport habc]
  exact le_trans hle (Finset.single_le_sum
    (fun p hp => mul_nonneg (le_max_left 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)))
      (Real.log_nonneg (by
        have hp1 : 1 ≤ p := le_trans (by norm_num : 1 ≤ 2)
          (prime_of_mem_arithmeticPrimeSupport (x := abcRationalPoint a c) hp).two_le
        exact_mod_cast hp1)))
    hq)

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

noncomputable section

/-- The index-cardinality cast is nonzero. -/
theorem cor312GapDict_sourceVolumeIndex_card_ne_zero (l : PrimeGeFive) :
    ((Fintype.card (SourceVolumeIndex l) : ℝ)) ≠ 0 := by
  have hpos := sourceVolumeIndex_card_pos l
  exact_mod_cast (ne_of_gt hpos)

/-- The `.toReal` of the singleton log-volume of a value point is the
truncated real log-degree: `max 0` of the point log-degree (the `ENNReal`
`ofReal` truncates negative log-degrees). -/
theorem cor312GapDict_singletonVolume_toReal_eq_max (v : V) (x : I.ThetaPilotPoint v) :
    (I.sourceSetVolume v {x}).toReal = max (I.sourceLocalLogDegree v x) 0 := by
  rw [I.cor312GapSupply_sourceSetVolume_singleton v x]
  unfold sourcePointVolume
  by_cases h : 0 ≤ I.sourceLocalLogDegree v x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp h)), ENNReal.toReal_zero,
      max_eq_right (le_of_lt (not_le.mp h))]

/-- **Exact form of the point-height dictionary.**  For any nonnegative bound
`H`, the truncated dictionary `(vol {x}).toReal ≤ H` is equivalent to the
untruncated degree inequality `logDegree x ≤ H`: no `ENNReal`/`toReal`
content remains on the left. -/
theorem cor312GapDict_singletonVolume_toReal_le_iff (v : V) (x : I.ThetaPilotPoint v)
    {H : ℝ} (hH : 0 ≤ H) :
    (I.sourceSetVolume v {x}).toReal ≤ H ↔ I.sourceLocalLogDegree v x ≤ H := by
  rw [I.cor312GapDict_singletonVolume_toReal_eq_max v x, max_le_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hH⟩⟩

/-- **Scaling separation.**  The weight dictionary at the scaled point
`λ * q` is equivalent to the additive separation of the two log-degrees: the
residual arithmetic obligation is `weight ≤ logDegree λ + logDegree q`.  Since
the frozen scaling field has nonpositive log-degree, this is strictly stronger
than the scaling-free form `weight ≤ logDegree q`. -/
theorem cor312GapDict_weightDictionary_iff_scalingSeparated (v : V)
    (lam q : I.ThetaPilotPoint v) (a c : Nat) :
    arithmeticWeight (abcRationalPoint a c) ≤ I.sourceLocalLogDegree v (lam * q) ↔
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v lam + I.sourceLocalLogDegree v q := by
  rw [I.sourceLocalLogDegree_mul v lam q]

/-- **Necessary condition for the weight dictionary.**  If the scaling has
nonpositive log-degree, the weight dictionary implies the scaling-free degree
domination `weight ≤ logDegree q`: any proof of the dictionary must at least
show that the point's own log-degree dominates the arithmetic weight. -/
theorem cor312GapDict_weightDictionary_implies_scalingFree (v : V)
    (lam q : I.ThetaPilotPoint v) (hlam : I.sourceLocalLogDegree v lam ≤ 0) {a c : Nat}
    (h : arithmeticWeight (abcRationalPoint a c) ≤ I.sourceLocalLogDegree v (lam * q)) :
    arithmeticWeight (abcRationalPoint a c) ≤ I.sourceLocalLogDegree v q := by
  rw [I.sourceLocalLogDegree_mul v lam q] at h
  linarith

/-- **Satisfiability of the weight dictionary.**  Under the degree faithfulness
of the realization on positive-real exponents, some point map satisfies the
weight dictionary at the fixed scaling: take the constant theta-pilot point
whose exponent cancels the scaling and carries the weight.  This shows the
dictionary has models at the source layer; it does not prove it for the
application's point map. -/
theorem cor312GapDict_exists_pointMap_weightDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hdeg : ∀ b : Real, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      ∀ a b c : Nat, IsABCTriple a b c →
        arithmeticWeight (abcRationalPoint a c) ≤
          I.sourceLocalLogDegree v (D.scaling * p a b c) := by
  refine ⟨fun a b c => I.constantThetaPilotPoint v R (Multiplicative.ofAdd
    ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
      (Fintype.card (SourceVolumeIndex l) : ℝ))), ?_⟩
  intro a b c habc
  change arithmeticWeight (abcRationalPoint a c) ≤
    I.sourceLocalLogDegree v (D.scaling *
      I.constantThetaPilotPoint v R (Multiplicative.ofAdd
        ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
          (Fintype.card (SourceVolumeIndex l) : ℝ))))
  rw [I.sourceLocalLogDegree_mul v D.scaling _, I.sourceLocalLogDegree_constant v R _ hdeg]
  have hmul : (Fintype.card (SourceVolumeIndex l) : ℝ) *
      ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
        (Fintype.card (SourceVolumeIndex l) : ℝ)) =
      arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling :=
    mul_div_cancel₀ _ (cor312GapDict_sourceVolumeIndex_card_ne_zero l)
  rw [hmul]
  linarith

/-- **Satisfiability of the point-height dictionary.**  Under the degree
faithfulness of the realization on positive-real exponents, some point map
satisfies `(vol {λ * p abc}).toReal ≤ logHeight₁ x` on all ABC triples: take the
constant point whose exponent cancels the scaling and carries the height. -/
theorem cor312GapDict_exists_pointMap_pointHeightDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hdeg : ∀ b : Real, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      ∀ a b c : Nat, IsABCTriple a b c →
        (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
          Height.logHeight₁ (abcRationalPoint a c) := by
  refine ⟨fun a b c => I.constantThetaPilotPoint v R (Multiplicative.ofAdd
    ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
      (Fintype.card (SourceVolumeIndex l) : ℝ))), ?_⟩
  intro a b c habc
  change (I.sourceSetVolume v {D.scaling *
    I.constantThetaPilotPoint v R (Multiplicative.ofAdd
      ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
        (Fintype.card (SourceVolumeIndex l) : ℝ)))}).toReal ≤
    Height.logHeight₁ (abcRationalPoint a c)
  have hdeg_eq : I.sourceLocalLogDegree v (D.scaling *
      I.constantThetaPilotPoint v R (Multiplicative.ofAdd
        ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
          (Fintype.card (SourceVolumeIndex l) : ℝ)))) =
      Height.logHeight₁ (abcRationalPoint a c) := by
    rw [I.sourceLocalLogDegree_mul v D.scaling _, I.sourceLocalLogDegree_constant v R _ hdeg]
    have hmul : (Fintype.card (SourceVolumeIndex l) : ℝ) *
        ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
          (Fintype.card (SourceVolumeIndex l) : ℝ)) =
        Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling :=
      mul_div_cancel₀ _ (cor312GapDict_sourceVolumeIndex_card_ne_zero l)
    rw [hmul]
    ring
  exact (I.cor312GapDict_singletonVolume_toReal_le_iff v _
    (cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc)).mpr (le_of_eq hdeg_eq)

/-- **The weight dictionary is not universal.**  Under degree faithfulness,
some point map violates the weight dictionary at any given ABC triple: the
constant point with exponent below `weight - logDegree λ` by one exceeds.
Hence the dictionary is a genuine hypothesis, not a theorem of the
definitions. -/
theorem cor312GapDict_weightDictionary_not_universal (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hdeg : ∀ b : Real, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    {a b c : Nat} (habc : IsABCTriple a b c) :
    ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      I.sourceLocalLogDegree v (D.scaling * p a b c) <
        arithmeticWeight (abcRationalPoint a c) := by
  refine ⟨fun _ _ _ => I.constantThetaPilotPoint v R (Multiplicative.ofAdd
    ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling - 1) /
      (Fintype.card (SourceVolumeIndex l) : ℝ))), ?_⟩
  change I.sourceLocalLogDegree v (D.scaling *
    I.constantThetaPilotPoint v R (Multiplicative.ofAdd
      ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling - 1) /
        (Fintype.card (SourceVolumeIndex l) : ℝ)))) <
    arithmeticWeight (abcRationalPoint a c)
  rw [I.sourceLocalLogDegree_mul v D.scaling _, I.sourceLocalLogDegree_constant v R _ hdeg]
  have hmul : (Fintype.card (SourceVolumeIndex l) : ℝ) *
      ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling - 1) /
        (Fintype.card (SourceVolumeIndex l) : ℝ)) =
      arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling - 1 :=
    mul_div_cancel₀ _ (cor312GapDict_sourceVolumeIndex_card_ne_zero l)
  rw [hmul]
  linarith

/-- **The point-height dictionary is not universal.**  Under degree
faithfulness, some point map violates the point-height dictionary at any given
ABC triple: the constant point with exponent one above `height - logDegree λ`
gives truncated volume `height + 1`. -/
theorem cor312GapDict_pointHeightDictionary_not_universal (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hdeg : ∀ b : Real, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    {a b c : Nat} (habc : IsABCTriple a b c) :
    ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      Height.logHeight₁ (abcRationalPoint a c) <
        (I.sourceSetVolume v {D.scaling * p a b c}).toReal := by
  refine ⟨fun _ _ _ => I.constantThetaPilotPoint v R (Multiplicative.ofAdd
    ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling + 1) /
      (Fintype.card (SourceVolumeIndex l) : ℝ))), ?_⟩
  change Height.logHeight₁ (abcRationalPoint a c) <
    (I.sourceSetVolume v {D.scaling *
      I.constantThetaPilotPoint v R (Multiplicative.ofAdd
        ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling + 1) /
          (Fintype.card (SourceVolumeIndex l) : ℝ)))}).toReal
  have hdeg_eq : I.sourceLocalLogDegree v (D.scaling *
      I.constantThetaPilotPoint v R (Multiplicative.ofAdd
        ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling + 1) /
          (Fintype.card (SourceVolumeIndex l) : ℝ)))) =
      Height.logHeight₁ (abcRationalPoint a c) + 1 := by
    rw [I.sourceLocalLogDegree_mul v D.scaling _, I.sourceLocalLogDegree_constant v R _ hdeg]
    have hmul : (Fintype.card (SourceVolumeIndex l) : ℝ) *
        ((Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling + 1) /
          (Fintype.card (SourceVolumeIndex l) : ℝ)) =
        Height.logHeight₁ (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling + 1 :=
      mul_div_cancel₀ _ (cor312GapDict_sourceVolumeIndex_card_ne_zero l)
    rw [hmul]
    ring
  rw [I.cor312GapDict_singletonVolume_toReal_eq_max v _, hdeg_eq,
    max_eq_left (by linarith [cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc])]
  linarith

/-- **`hpoint` from the minimal premise.**  The truncated dictionary
`(vol {λ * q}).toReal ≤ height` is equivalent (height nonnegative) to the
untruncated `logDegree (λ * q) ≤ height`; composing the untruncated form with
the H1 valuation-bound reduction yields the `hpoint` input of the gap-2
assembly with `D₁ = 0`, at the value-realized carrier.  This is the attachment
point of the point-height dictionary to the frozen consumers; consumption of
`cor312Gap2_pointBound_of_singletonVolume_le_logHeight` only, no frozen file
is modified. -/
theorem cor312GapDict_sourcePointBound_of_degree_le_height (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (hline : ∀ a b c : Nat, IsABCTriple a b c →
      I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) := by
  have hvolheight : ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
        Height.logHeight₁ (abcRationalPoint a c) := by
    intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      Height.logHeight₁ (abcRationalPoint a c)
    exact (I.cor312GapDict_singletonVolume_toReal_le_iff v _
      (cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc)).mpr (hline a b c habc)
  intro a b c habc
  exact cor312Gap2_pointBound_of_singletonVolume_le_logHeight
    (I.sourceUnitRegionHaarInterface v R n D) p heps hvolheight hval a b c habc

/-- **`hpoint` from the minimal premise, additive form (version-2 mirror of
`cor312GapDict_sourcePointBound_of_degree_le_height`).**  Same truncated
point-height dictionary and same carrier datum; the refuted uniform valuation
bound is replaced by the approved additive input
`height ≤ (1 + ε) · weight + A` (contract `ABCHeightWeightAdditiveBoundV2`),
and the `hpoint` input is produced with the explicit constant `D₁ = A`.  The
`0 ≤ eps` slot is retained for shape parity with the original declaration; the
additive composition itself does not consume it. -/
theorem cor312GapDict_sourcePointBound_of_additiveBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps A : ℝ} (heps : 0 ≤ eps)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hline : ∀ a b c : Nat, IsABCTriple a b c →
      I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A := by
  have hvolheight : ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
        Height.logHeight₁ (abcRationalPoint a c) := by
    intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      Height.logHeight₁ (abcRationalPoint a c)
    exact (I.cor312GapDict_singletonVolume_toReal_le_iff v _
      (cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc)).mpr (hline a b c habc)
  intro a b c habc
  exact cor312Gap2_pointBound_of_singletonVolume_le_logHeight_of_additiveBound
    (I.sourceUnitRegionHaarInterface v R n D) p hvolheight hadd a b c habc

end

end OriginalInput
end Theorem311Source

end LeanFormal.IUT
