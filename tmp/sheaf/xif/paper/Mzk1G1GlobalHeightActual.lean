import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GlobalHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
/-- Route §13.3 global height step: the actual all-compact Belyi uniform-ε
criterion plus the Frey height bound data produce the global uniform radical
height bound. -/
theorem globalHeightBound_of_uniformEpsilon_and_freyHeight
    (hUniform : UniformEpsilonCriterionRatAll belyiAllCompactSequence)
    (H : ∀ ε : ℝ, 0 < ε → FreyHeightBound ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c →
        Nat.Coprime a b →
        (c : ℝ) ≤ C * (radical (a * b * c) : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := H ε hε
  refine ⟨C, hC, ?_⟩
  intro a b c ha hb hc hab hcop
  have h := hbound a b c ha hb hc hab hcop
  simpa [freyConductor] using h
/-- Route §13.3 global assembly: uniform-ε compactness plus Frey height data
give the global ABC elliptic height criterion. -/
theorem globalABCCriterion_of_uniformEpsilon_and_freyHeight
    (hUniform : UniformEpsilonCriterionRatAll belyiAllCompactSequence)
    (H : ∀ ε : ℝ, 0 < ε → FreyHeightBound ε) :
    ABCEllipticHeightCriterionAll :=
  criterionAll_of_uniformEpsilon_and_freyHeight hUniform H
#print axioms globalHeightBound_of_uniformEpsilon_and_freyHeight
#print axioms globalABCCriterion_of_uniformEpsilon_and_freyHeight
end LeanFormal.IUT.XiFPaper.Mzk1G1GlobalHeightActual
end