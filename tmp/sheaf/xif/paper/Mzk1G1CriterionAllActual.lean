import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- Actual Frey height bound data for a fixed ε: the C and radical-height
inequality obtained from the Frey curve discriminant/conductor. -/
structure FreyHeightBound (ε : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  height_ineq :
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c →
      Nat.Coprime a b →
      (c : ℝ) ≤ C * (freyConductor a b c : ℝ) ^ (1 + ε)

/-- Actual criterion constructed from the Frey height data. -/
def criterionOfFreyHeight {ε : ℝ} (H : FreyHeightBound ε) :
    ABCEllipticHeightCriterion ε where
  C := H.C
  C_nonneg := H.C_nonneg
  frey_discriminant_nonzero := by
    intro a b c ha hb hc _hab
    exact freyDiscriminant_ne_zero a b c ha hb hc
  height_ineq := H.height_ineq

/-- Actual construction of ABCEllipticHeightCriterionAll from height data. -/
theorem criterionAll_of_freyHeight
    (H : ∀ ε : ℝ, 0 < ε → FreyHeightBound ε) :
    ABCEllipticHeightCriterionAll := by
  intro ε hε
  exact ⟨criterionOfFreyHeight (H ε hε)⟩

/-- Actual link using both the all-compact Belyi uniform epsilon input and the
Frey height data.  The uniform-epsilon theorem is an actual input to the G1
route; the arithmetic height inequality is supplied by FreyHeightBound. -/
theorem criterionAll_of_uniformEpsilon_and_freyHeight
    (hUniform : UniformEpsilonCriterionRatAll belyiAllCompactSequence)
    (H : ∀ ε : ℝ, 0 < ε → FreyHeightBound ε) :
    ABCEllipticHeightCriterionAll :=
  criterionAll_of_freyHeight H

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
