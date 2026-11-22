import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVLiteralCarrierReductionActual — literal product-carrier comparison reduction

A481 route: on the literal finite product of local fields (restricted product of
log-shell/local-field data with Haar measure), the comparison region is a
multiplicative dilate of the unit region.  Its normalized log-volume is computed
by the Haar character (normalizedLogVolume_smul, normalizedLogVolume_unitRegion),
not by a value-realized model.  Hence the two IUT IV comparison inequalities reduce
exactly to the concrete Haar-normalization inequalities `LiteralHeightComparison`
and `LiteralMainEstimate`; the arithmetic inputs remain explicit named inputs.
No closure is claimed; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVLiteralCarrierReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldProductHull
open MeasureTheory

universe u

variable {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, NormedField (K i)]
  [∀ i, ProperSpace (K i)]
  [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
  (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]
  (hpos : 0 < μ (unitRegion (K := K)))
  (hfin : μ (unitRegion (K := K)) < ⊤)

local instance scalingUnitsSmul : SMul ((i : ι) → (K i))ˣ ((i : ι) → K i) :=
  ⟨fun u x i => (u : (i : ι) → K i) i * x i⟩

/-- On the literal product carrier, the normalized log-volume of a multiplicative
dilate of the unit region is exactly the logarithm of the Haar character. -/
theorem normalizedLogVolume_region_eq_log_char
    (hpos : 0 < μ (unitRegion (K := K)))
    (hfin : μ (unitRegion (K := K)) < ⊤)
    (lam : (i : ι) → K i)
    (hlam : ∀ i, lam i ≠ 0) :
    normalizedLogVolume μ (region (K := K) lam) =
      Real.log (distribHaarChar ((i : ι) → K i) (scalingUnits lam hlam) : ℝ) :=
  normalizedLogVolume_region (K := K) μ lam hlam

/-- The literal-carrier height comparison: height is bounded by (1+eps) times the
log Haar-character of the dilate. -/
def LiteralHeightComparison (height : Nat → Nat → Nat → ℝ) (eps : ℝ)
    (lam : Nat → Nat → Nat → (i : ι) → K i)
    (hlam : ∀ a b c i, lam a b c i ≠ 0) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    height a b c ≤ (1 + eps) *
      Real.log (distribHaarChar ((i : ι) → K i)
        (scalingUnits (lam a b c) (hlam a b c)) : ℝ)

/-- The literal-carrier main estimate: the log Haar-character of the dilate is bounded
by (1+eps) times the arithmetic weight plus the hull log-volume and a constant. -/
def LiteralMainEstimate (weight : Nat → Nat → Nat → ℝ) (eps D : ℝ)
    (H : Set ((i : ι) → K i))
    (lam : Nat → Nat → Nat → (i : ι) → K i)
    (hlam : ∀ a b c i, lam a b c i ≠ 0) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Real.log (distribHaarChar ((i : ι) → K i)
      (scalingUnits (lam a b c) (hlam a b c)) : ℝ) ≤
      (1 + eps) * weight a b c + normalizedLogVolume μ H + D

/-- Gap 1 on the literal carrier is exactly the concrete Haar-character height
comparison. -/
theorem literalGap1_iff (height : Nat → Nat → Nat → ℝ) (eps : ℝ)
    (lam : Nat → Nat → Nat → (i : ι) → K i)
    (hlam : ∀ a b c i, lam a b c i ≠ 0)
    (hpos : 0 < μ (unitRegion (K := K)))
    (hfin : μ (unitRegion (K := K)) < ⊤) :
    (∀ a b c : Nat, IsABCTriple a b c →
      height a b c ≤ (1 + eps) *
        normalizedLogVolume μ (region (K := K) (lam a b c))) ↔
      LiteralHeightComparison (K := K) height eps lam hlam := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    rwa [normalizedLogVolume_region_eq_log_char (μ := μ) (hpos := hpos) (hfin := hfin) (lam a b c) (hlam a b c)] at hh
  · intro h a b c habc
    have hh := h a b c habc
    rwa [normalizedLogVolume_region_eq_log_char (μ := μ) (hpos := hpos) (hfin := hfin) (lam a b c) (hlam a b c)]

/-- Gap 2 on the literal carrier is exactly the concrete Haar-character main
estimate. -/
theorem literalGap2_iff (weight : Nat → Nat → Nat → ℝ) (eps D : ℝ)
    (H : Set ((i : ι) → K i))
    (lam : Nat → Nat → Nat → (i : ι) → K i)
    (hlam : ∀ a b c i, lam a b c i ≠ 0)
    (hpos : 0 < μ (unitRegion (K := K)))
    (hfin : μ (unitRegion (K := K)) < ⊤) :
    (∀ a b c : Nat, IsABCTriple a b c →
      normalizedLogVolume μ (region (K := K) (lam a b c)) ≤
        (1 + eps) * weight a b c + normalizedLogVolume μ H + D) ↔
      LiteralMainEstimate (K := K) μ weight eps D H lam hlam := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    rwa [normalizedLogVolume_region_eq_log_char (μ := μ) (hpos := hpos) (hfin := hfin) (lam a b c) (hlam a b c)] at hh
  · intro h a b c habc
    have hh := h a b c habc
    rwa [normalizedLogVolume_region_eq_log_char (μ := μ) (hpos := hpos) (hfin := hfin) (lam a b c) (hlam a b c)]

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVLiteralCarrierReductionActual

end
