import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BelyiProducerImpliesABCACtual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
/-- If the requested Belyi-compactness-to-Frey-height producer existed, then
ABC would be a theorem: the uniform-ε hypothesis is itself unconditional
(`belyiAllCompactSequence_uniformEpsilon`). -/
theorem belyiProducer_implies_ABC
    (h : UniformEpsilonCriterionRatAll belyiAllCompactSequence →
      ∀ ε : ℝ, 0 < ε → Nonempty (FreyHeightBound ε)) :
    ABCStatement := by
  have huni : UniformEpsilonCriterionRatAll belyiAllCompactSequence :=
    belyiAllCompactSequence_uniformEpsilon
  have H : ∀ ε : ℝ, 0 < ε → FreyHeightBound ε :=
    fun ε hε => Classical.choice (h huni ε hε)
  exact abcStatement_of_ellipticHeightCriterion (criterionAll_of_freyHeight H)
#print axioms belyiProducer_implies_ABC
end LeanFormal.IUT.XiFPaper.Mzk1BelyiProducerImpliesABCACtual
end