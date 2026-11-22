import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4TripleDependentScalingActual (stage4 lane; interface design)

A620 module: design of the TRIPLE-DEPENDENT scaling interface — a scale function
`Nat → Nat → Nat → ℝ` with positivity and coordinatewise monotonicity, the induced
comparison regions (closed balls), and their monotonicity/volume monotonicity.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleDependentScalingActual

open MeasureTheory
open scoped ENNReal

/-- Triple-dependent scaling interface. -/
structure TripleDependentScaling where
  /-- the scalar scale of a triple. -/
  scale : Nat → Nat → Nat → Real
  /-- positivity. -/
  scale_pos : ∀ a b c, 0 < scale a b c
  /-- coordinatewise monotonicity. -/
  scale_mono : ∀ {a b c a' b' c' : Nat}, a ≤ a' → b ≤ b' → c ≤ c' →
    scale a b c ≤ scale a' b' c'

/-- The comparison region of a triple: the closed ball of the scale. -/
noncomputable def tripleBall (s : TripleDependentScaling) (a b c : Nat) : Set Real :=
  Metric.closedBall (0 : Real) (s.scale a b c)

/-- Coordinatewise monotonicity of the comparison regions. -/
theorem tripleBall_mono (s : TripleDependentScaling)
    {a b c a' b' c' : Nat} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    tripleBall s a b c ⊆ tripleBall s a' b' c' :=
  Metric.closedBall_subset_closedBall (s.scale_mono ha hb hc)

/-- Volume monotonicity of the comparison regions. -/
theorem tripleBall_volume_mono (s : TripleDependentScaling)
    {a b c a' b' c' : Nat} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    volume (tripleBall s a b c) ≤ volume (tripleBall s a' b' c') :=
  measure_mono (tripleBall_mono s ha hb hc)

/-- The constant scaling instance. -/
noncomputable def constantScaling (x : Real) (hx : 0 < x) : TripleDependentScaling where
  scale := fun _ _ _ => x
  scale_pos := fun _ _ _ => hx
  scale_mono := by
    intro a b c a' b' c' ha hb hc
    exact le_refl x

/-- The constant scaling's value. -/
theorem constantScaling_scale (x : Real) (hx : 0 < x) (a b c : Nat) :
    (constantScaling x hx).scale a b c = x :=
  rfl

#check TripleDependentScaling
#check tripleBall
#check tripleBall_mono
#check tripleBall_volume_mono
#check constantScaling
#check constantScaling_scale

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleDependentScalingActual
end
