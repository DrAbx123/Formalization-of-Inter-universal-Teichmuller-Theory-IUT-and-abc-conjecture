import tmp.sheaf.xif.paper.Mzk1G1GlobalHeightActual
import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1HeightProducerChainActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
/-- G1 height producer chain: uniform-ε compactness plus Frey height data
give the global radical height bound. -/
theorem heightProducerChain
    (hUniform : UniformEpsilonCriterionRatAll belyiAllCompactSequence)
    (H : ∀ ε : ℝ, 0 < ε → FreyHeightBound ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c →
        Nat.Coprime a b →
        (c : ℝ) ≤ C * (radical (a * b * c) : ℝ) ^ (1 + ε) :=
  LeanFormal.IUT.XiFPaper.Mzk1G1GlobalHeightActual.globalHeightBound_of_uniformEpsilon_and_freyHeight hUniform H
#print axioms heightProducerChain
end LeanFormal.IUT.XiFPaper.Mzk1G1HeightProducerChainActual
end