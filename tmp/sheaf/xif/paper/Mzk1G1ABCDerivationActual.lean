import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import tmp.sheaf.xif.paper.Mzk1G1ABCCompactnessActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- Attempted actual derivation of ABCStatement from all-compact Belyi
uniform epsilon.  The missing input is the elliptic-height/radical criterion. -/
theorem abcStatement_of_belyiUniformEpsilon
    (h : UniformEpsilonCriterionRatAll belyiAllCompactSequence) :
    ABCStatement := by
  intro ε hε
  exact ?_

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
