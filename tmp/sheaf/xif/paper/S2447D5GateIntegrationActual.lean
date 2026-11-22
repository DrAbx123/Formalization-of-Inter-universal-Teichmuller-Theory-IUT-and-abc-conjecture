import tmp.sheaf.xif.paper.S2445D5LargeImageChainActual
import tmp.sheaf.xif.paper.S2442QE5DegreeOrderSubagentActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2447D5GateIntegrationActual

open LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual
open LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual

/-- The D5 exact missing, after separating the refuted degree target: pair
transitivity plus cycle type at the actual basis. -/
def S2447D5ExactFirstMissing : Prop :=
  S2445GroupRouteExact

/-- D5 target from the exact pair/cycle missing. -/
theorem S2447D5LargeImageFive_of_exact
    (h : S2447D5ExactFirstMissing) : S1987D5LargeImageFive :=
  S2445D5LargeImageFive_of_groupRouteExact h

/-- The degree=image-order target is refuted under the projective bridge and
the standard image hypotheses. -/
theorem S2447DegreeEqImageOrder_refuted
    (D : S2442Psi5ProjectiveBridge)
    (hdet : S2445RangeDetSurjective)
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    ¬ S2445DegreeEqImageOrder :=
  S2442NotS2445DegreeEqImageOrder D hdet hpair hcycle

/-- Under the bridge the true degree of the psi5 splitting field is 240. -/
theorem S2447CorrectedDegree_eq_240
    (D : S2442Psi5ProjectiveBridge) :
    Module.finrank ℚ s2289QE5 = 240 :=
  S2442Degree_eq_240 D

/-- Pair transitivity remains implied by the image-tail input and by the
twelve-cycle input. -/
theorem S2447PairTransitive_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2445RangePairTransitive :=
  S2445RangePairTransitive_of_twelveCycle h

end LeanFormal.IUT.XiFPaper.S2447D5GateIntegrationActual

end
