import tmp.sheaf.xif.paper.S2447D5GateIntegrationActual
import tmp.sheaf.xif.paper.S2442QE5DegreeOrderSubagentActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2445D5LargeImageChainActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2449D5FinalStatusActual

open LeanFormal.IUT.XiFPaper.S2447D5GateIntegrationActual
open LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual

/-- The D5 large-image exact first missing after the gate: actual range pair
transitivity and actual range cycle type (10,2), at the selected basis. -/
def S2449D5ExactFirstMissing : Prop :=
  S2445GroupRouteExact

/-- Conditional D5 final theorem from the exact pair/cycle data. -/
theorem S2449D5LargeImageFive_of_exact
    (h : S2449D5ExactFirstMissing) : S1987D5LargeImageFive :=
  S2445D5LargeImageFive_of_groupRouteExact h

/-- The original S2445 exact conjunction, which included degree = image order,
is refuted under the projective bridge and the standard image hypotheses. -/
theorem S2449OriginalS2445Exact_refuted
    (D : S2442Psi5ProjectiveBridge)
    (hdet : S2445RangeDetSurjective)
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    ¬ S2445ExactFirstMissing := by
  intro h
  exact S2442NotS2445DegreeEqImageOrder D hdet hpair hcycle h.2.2.2

/-- The corrected true degree under the projective bridge is 240. -/
theorem S2449CorrectedDegree_eq_240
    (D : S2442Psi5ProjectiveBridge) :
    Module.finrank ℚ s2289QE5 = 240 :=
  S2442Degree_eq_240 D

/-- The actual range pair transitivity is implied by the twelve-cycle input
and by the image-tail input (S2440). -/
theorem S2449PairTransitive_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2445RangePairTransitive :=
  S2445RangePairTransitive_of_twelveCycle h

end LeanFormal.IUT.XiFPaper.S2449D5FinalStatusActual

end
