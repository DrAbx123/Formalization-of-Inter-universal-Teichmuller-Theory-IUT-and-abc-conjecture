import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual
import tmp.sheaf.xif.paper.S2364D5GroupRouteActual
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2298QE5OrderActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2301DegreeEqOrderActual
import tmp.sheaf.xif.paper.S2289QE5DegreeActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual

open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2298QE5OrderActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- Actual range pair transitivity at the selected basis. -/
def S2445RangePairTransitive : Prop :=
  S2203RangePairTransitiveRequired S1982Basis

/-- Actual range cycle type (10,2) at the selected basis. -/
def S2445RangeCycleType : Prop :=
  S2203RangeCycleTypeRequired S1982Basis

/-- Determinant surjectivity of the actual range. -/
def S2445RangeDetSurjective : Prop :=
  DetSurjectiveOn
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

/-- Degree = image order for the actual absolute 5-division field. -/
def S2445DegreeEqImageOrder : Prop :=
  Module.finrank ℚ s2289QE5 =
    Nat.card (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

/-- Exact first missing conjunction for the full D5 chain. -/
def S2445ExactFirstMissing : Prop :=
  S2445RangePairTransitive ∧
    S2445RangeCycleType ∧
      S2445RangeDetSurjective ∧ S2445DegreeEqImageOrder

/-- Consumer: pair transitivity plus cycle type gives the D5 target. -/
theorem S2445D5LargeImageFive_of_pair_cycle
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle hpair

/-- Actual image order 480 under the three standard range hypotheses. -/
theorem S2445ImageOrder_eq_480
    (hdet : S2445RangeDetSurjective)
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    Nat.card (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range = 480 :=
  S2298ImageCard_eq_480_of_hypotheses _ hdet hpair hcycle

/-- Actual Q(E[5]) degree 480 from the exact degree/image-order identification
and the three range hypotheses. -/
theorem S2445QE5Degree_eq_480
    (hdet : S2445RangeDetSurjective)
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType)
    (hdeg : S2445DegreeEqImageOrder) :
    Module.finrank ℚ s2289QE5 = 480 := by
  rw [hdeg, S2445ImageOrder_eq_480 hdet hpair hcycle]

/-- Full-chain consumer: the exact conjunction gives the D5 target and the
degree computation. -/
theorem S2445Consumers_of_exact
    (h : S2445ExactFirstMissing) :
    S1987D5LargeImageFive ∧ Module.finrank ℚ s2289QE5 = 480 :=
  ⟨S2445D5LargeImageFive_of_pair_cycle h.1 h.2.1,
    S2445QE5Degree_eq_480 h.2.2.1 h.1 h.2.1 h.2.2.2⟩


/-- Range-top stronger condition from S2378 gives pair transitivity. -/
theorem S2445PairTransitive_of_rangeTop
    (h : S2378RangeTopRequired) : S2445RangePairTransitive :=
  S2378PairTransitive_of_rangeTop h

/-- Range-top stronger condition gives the D5 target. -/
theorem S2445D5LargeImageFive_of_rangeTop
    (h : S2378RangeTopRequired) : S1987D5LargeImageFive :=
  S2378D5LargeImageFive_of_rangeTop h

/-- The group route's image-tail conclusion from pair transitivity and cycle type. -/
theorem S2445ImageTail_of_pair_cycle
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    S1725ImageTail S1987Five S1982Basis :=
  S2364RangeImageTail_of_hypotheses S1982Basis hcycle hpair

/-- The group-route exact conjunction (pair transitivity and cycle type). -/
def S2445GroupRouteExact : Prop :=
  S2445RangePairTransitive ∧ S2445RangeCycleType

/-- Group-route consumer. -/
theorem S2445D5LargeImageFive_of_groupRouteExact
    (h : S2445GroupRouteExact) : S1987D5LargeImageFive :=
  S2445D5LargeImageFive_of_pair_cycle h.1 h.2


/-- The integrated pair-transitivity target is exactly S2378's exact missing. -/
theorem S2445PairTransitive_iff_S2378 :
    S2445RangePairTransitive ↔ S2378ExactFirstMissing :=
  Iff.rfl

/-- The integrated group-route conjunction is exactly S2364's exact missing. -/
theorem S2445GroupRouteExact_iff_S2364 :
    S2445GroupRouteExact ↔ S2364ExactFirstMissing := by
  constructor
  · rintro ⟨hpair, hcycle⟩
    exact ⟨hcycle, hpair⟩
  · rintro ⟨hcycle, hpair⟩
    exact ⟨hpair, hcycle⟩

/-- The strong range-top condition is a sufficient consumer of the pair target. -/
theorem S2445RangeTop_implies_pair :
    S2378RangeTopRequired → S2445RangePairTransitive :=
  S2445PairTransitive_of_rangeTop


/-- Subagent A consumer: the twelve-cycle input implies the integrated pair target. -/
theorem S2445RangePairTransitive_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2445RangePairTransitive :=
  S2440RangePairTransitive_of_twelveCycle h

/-- Subagent A consumer: the image-tail input implies the integrated pair target. -/
theorem S2445RangePairTransitive_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) : S2445RangePairTransitive :=
  S2440RangePairTransitive_of_imageTail h

end LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual

end
