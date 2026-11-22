import tmp.sheaf.xif.paper.S2375RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2209D5RangeProofActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual

open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2209D5RangeProofActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The stronger sufficient condition: the actual mod-5 range is the whole
GL2. -/
def S2378RangeTopRequired : Prop :=
  (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range = ⊤

/-- Full range implies pair transitivity. -/
theorem S2378PairTransitive_of_rangeTop
    (h : S2378RangeTopRequired) :
    S2375RangePairTransitiveRequired := by
  unfold S2375RangePairTransitiveRequired S2203RangePairTransitiveRequired
  rw [h]
  exact pairTransitive_top

/-- Full range gives the D5 target directly. -/
theorem S2378D5LargeImageFive_of_rangeTop
    (h : S2378RangeTopRequired) : S1987D5LargeImageFive :=
  S2209D5LargeImageFive_of_rangeTop S1982Basis h

/-- Exact first missing remains the weaker actual range pair transitivity. -/
def S2378ExactFirstMissing : Prop :=
  S2375ExactFirstMissing
/-- Conditional D5 from the exact pair-transitivity plus cycle type. -/
theorem S2378D5LargeImageFive_of_exact
    (h : S2378ExactFirstMissing)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2375D5LargeImageFive_of_exact h hcycle

end LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual

end
