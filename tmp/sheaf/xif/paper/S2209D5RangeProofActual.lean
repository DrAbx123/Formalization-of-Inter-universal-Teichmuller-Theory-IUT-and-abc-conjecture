import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2209D5RangeProofActual

open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The exact cycle-type hypothesis for the actual range at a basis. -/
def S2209RangeCycleTypeRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2203RangeCycleTypeRequired b

/-- The exact pair-transitivity hypothesis for the actual range at a basis. -/
def S2209RangePairTransitiveRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2203RangePairTransitiveRequired b

/-- The exact first missing conjunction for the actual range. -/
def S2209ExactFirstMissing
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2209RangeCycleTypeRequired b ∧ S2209RangePairTransitiveRequired b

/-- Actual conditional assembly: the exact first missing gives the S1987 D5
target. -/
theorem S2209D5LargeImageFive_of_exactFirstMissing
    (b : S1725TorsionBasis S1987Five)
    (h : S2209ExactFirstMissing b) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses b h.1 h.2

/-- If the actual mod-5 range is the whole group, the cycle-type hypothesis
is automatic (S2009). -/
theorem S2209RangeCycleType_of_rangeTop
    (b : S1725TorsionBasis S1987Five)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤) :
    S2209RangeCycleTypeRequired b := by
  unfold S2209RangeCycleTypeRequired S2203RangeCycleTypeRequired
  rw [h]
  exact hasCycleType102_top

/-- If the actual mod-5 range is the whole group, pair transitivity is
automatic (S2009). -/
theorem S2209RangePairTransitive_of_rangeTop
    (b : S1725TorsionBasis S1987Five)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤) :
    S2209RangePairTransitiveRequired b := by
  unfold S2209RangePairTransitiveRequired S2203RangePairTransitiveRequired
  rw [h]
  exact pairTransitive_top

/-- Actual full-range consumer: range = top gives D5 directly through the
range-hypothesis assembly. -/
theorem S2209D5LargeImageFive_of_rangeTop
    (b : S1725TorsionBasis S1987Five)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤) :
    S1987D5LargeImageFive :=
  S2209D5LargeImageFive_of_exactFirstMissing b
    ⟨S2209RangeCycleType_of_rangeTop b h,
      S2209RangePairTransitive_of_rangeTop b h⟩

end LeanFormal.IUT.XiFPaper.S2209D5RangeProofActual

end
