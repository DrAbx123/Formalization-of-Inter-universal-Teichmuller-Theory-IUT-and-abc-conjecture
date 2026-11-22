import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual

/-!
# A594 volume-estimate intermediate lemmas (shehdd)

Numerical reductions for the second IUT IV Thm 1.10 estimate (the volume/
arithmetic-weight bound).  Objects are not changed; these are pure real lemmas
plus the standard implication from an additive bound to the volume estimate.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesVolumeLemmasShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

/-- Monotonicity in `δ` for the volume estimate (weights nonnegative). -/
theorem volume_estimate_mono_delta {v w hull D δ0 δ : Real}
    (hw : 0 ≤ w) (hδ0 : 0 < δ0) (hδ : δ0 ≤ δ)
    (h : v ≤ (1 + δ0) * w + hull + D) :
    v ≤ (1 + δ) * w + hull + D := by
  have hle : (1 + δ0) * w ≤ (1 + δ) * w :=
    mul_le_mul_of_nonneg_right (by linarith) hw
  linarith

/-- A pointwise additive bound `v <= w + hull + D` implies the volume-estimate
shape `v <= (1+δ)*w + hull + D` for every `δ > 0`, provided `w >= 0`. -/
theorem volume_estimate_of_additive_bound {v w hull D δ : Real}
    (hw : 0 ≤ w) (hδ : 0 < δ) (h : v ≤ w + hull + D) :
    v ≤ (1 + δ) * w + hull + D := by
  have hwδ : 0 ≤ δ * w := mul_nonneg (le_of_lt hδ) hw
  nlinarith

/-- Pointwise form over ABC triples: an additive bound on the log-volume gives
the full `volume_estimate` slot of `ABCTwoEstimates` (with the same `D`). -/
theorem volume_estimate_of_additive_bound_of_triples {logVolume : Nat → Nat → Nat → Real}
    {hullVolume D : Real}
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ arithmeticWeight (abcRationalPoint a c) + hullVolume + D) :
    ∀ δ : Real, 0 < δ → ∃ D' : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D' := by
  intro δ hδ
  refine ⟨D, ?_⟩
  intro a b c htriple
  exact volume_estimate_of_additive_bound
    (arithmeticWeight_nonneg_local (abcRationalPoint a c)) hδ (h a b c htriple)

/-- Numeric evidence: zero log-volume and zero hull-volume satisfy the volume
estimate with `D = 0` (weights nonnegative). -/
theorem zero_volume_estimate' :
    ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (0 : Real) ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) + 0 + D := by
  intro δ hδ
  refine ⟨(0 : Real), ?_⟩
  intro a b c _
  simpa using mul_nonneg (by linarith : (0 : Real) ≤ 1 + δ)
    (arithmeticWeight_nonneg_local (abcRationalPoint a c))

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesVolumeLemmasShaActual
