import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
/-- Uniform ABC point-height criterion. -/
def P8PointHeightCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B
theorem p8_pointHeightCriterion_iff_freyJ :
    P8PointHeightCriterion ↔ ABCFreyJProductHeightCriterion := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨B, hB⟩
    refine ⟨6 * B + Real.log 256, ?_⟩
    intro a b c habc
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple habc
    have hp := hB a b c habc
    have hj := (rationalFreyWeierstrassCurve_height_upper_bound_transfers habc
      ((1 + ε) * Real.log (radical (a * b * c) : ℝ) + B)).2.2.2 hp
    nlinarith
  · intro h ε hε
    rcases h ε hε with ⟨B, hB⟩
    refine ⟨(B - Real.log (27 / 64 : ℝ)) / 6, ?_⟩
    intro a b c habc
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple habc
    have hj := hB a b c habc
    have hp := (rationalFreyWeierstrassCurve_height_upper_bound_transfers habc
      (6 * (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B)).2.2.1
      (by nlinarith [hj])
    nlinarith
#print axioms p8_pointHeightCriterion_iff_freyJ
end LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
end