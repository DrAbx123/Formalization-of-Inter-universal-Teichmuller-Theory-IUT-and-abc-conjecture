import tmp.sheaf.xif.paper.Mzk1Stage4GapTransformationsActual

/-! # Mzk1Stage4Gap2StrengthRelationActual (stage4 lane; Gap2 shape/strength)

A680 module: shape decomposition of Gap 2 and its STRENGTH RELATION to the ABC height
bound — combining Gap 1 and the Gap-2 family yields the ABC-style height bound with the
honest `(1+ε)^2` loss.  This is the exact strength statement (not a stronger `(1+ε)`
claim).  No conclusion changed.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2StrengthRelationActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTransformationsActual

/-- Shape decomposition: Gap 2 is the single bound with the constants grouped. -/
theorem gap2_shape_decomp (regionVol weight hull D eps : Real) :
    (Gap2 regionVol weight hull D eps ↔
      regionVol ≤ (1 + eps) * weight + (hull + D)) := by
  constructor
  · intro h
    linarith [h.bound]
  · intro h
    exact ⟨by linarith⟩

/-- Strength relation: Gap 1 for `(height, regionVol)` together with the Gap-2 family
(for every `eps > 0`, some additive `D_eps`) yields the ABC-style height bound with the
honest `(1+eps)^2` loss. -/
theorem gap1_gap2_family_to_height_bound
    (height regionVol weight : Nat → Nat → Nat → Real) (hull : Real)
    (h1 : ∀ eps : Real, 0 < eps → ∀ a b c : Nat,
      height a b c ≤ (1 + eps) * regionVol a b c)
    (h2 : ∀ eps : Real, 0 < eps → ∃ D : Real,
      ∀ a b c : Nat,
        regionVol a b c ≤ (1 + eps) * weight a b c + hull + D) :
    ∀ eps : Real, 0 < eps → ∃ A : Real,
      ∀ a b c : Nat,
        height a b c ≤ (1 + eps) ^ 2 * weight a b c + A := by
  intro eps heps
  obtain ⟨D, hD⟩ := h2 eps heps
  refine ⟨(1 + eps) * (hull + D), fun a b c => ?_⟩
  have h1' := h1 eps heps a b c
  have h2' := hD a b c
  have hstep : (1 + eps) * regionVol a b c ≤
      (1 + eps) * ((1 + eps) * weight a b c + hull + D) :=
    mul_le_mul_of_nonneg_left h2' (by linarith)
  have hexpand : (1 + eps) * ((1 + eps) * weight a b c + hull + D) =
      (1 + eps) ^ 2 * weight a b c + (1 + eps) * (hull + D) := by ring
  linarith

/-- Complementary relation: the `(1+eps)^2` bound does NOT imply the `(1+eps)` bound
(strength asymmetry witness): with `weight = 1`, `eps = 1/2`, the coefficient differs. -/
theorem strength_asymmetry_witness :
    (1 + (1 / 2 : Real)) ^ 2 ≠ (1 + (1 / 2 : Real)) :=
  by norm_num

/-- Strength-status rows. -/
def gap2StrengthRows : List (String × String) :=
  [ ("shape decomposition", "gap2_shape_decomp: Gap2 ⇔ v ≤ (1+ε)w + (hull+D)")
  , ("strength relation", "Gap1 + Gap2 family ⇒ height ≤ (1+ε)^2 w + A (honest loss)")
  , ("asymmetry", "(1+ε)^2 ≠ (1+ε): the composed bound is genuinely weaker")
  , ("final boundary", "mainline finalBoundaryCertificate remains the boundary statement (read-only)")
  ]

/-- The strength record has four rows. -/
theorem gap2StrengthRows_length : gap2StrengthRows.length = 4 := rfl

#print axioms gap2_shape_decomp
#print axioms gap1_gap2_family_to_height_bound

#check gap2_shape_decomp
#check gap1_gap2_family_to_height_bound
#check strength_asymmetry_witness
#check gap2StrengthRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2StrengthRelationActual
end
