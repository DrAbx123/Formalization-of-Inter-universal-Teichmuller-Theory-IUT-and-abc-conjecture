import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2203D5RangeActual

open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- The cycle-type hypothesis on the actual mod-5 range at a basis. -/
def S2203RangeCycleTypeRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  HasCycleType102
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

/-- The twelve-pair transitivity hypothesis on the actual mod-5 range. -/
def S2203RangePairTransitiveRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  PairTransitive
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

/-- Exact first missing conjunction for the range inputs. -/
def S2203ExactFirstMissing
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2203RangeCycleTypeRequired b ∧ S2203RangePairTransitiveRequired b

/-- Actual conditional D5 assembly: the two range hypotheses give the S1987
D5 large-image target via S2132/S2020. -/
theorem S2203D5LargeImageFive_of_rangeHypotheses
    (b : S1725TorsionBasis S1987Five)
    (h102 : S2203RangeCycleTypeRequired b)
    (htrans : S2203RangePairTransitiveRequired b) :
    S1987D5LargeImageFive :=
  S2132D5LargeImageFive_of_rangeHypotheses b h102 htrans

/-- The same assembly from the exact conjunction. -/
theorem S2203D5LargeImageFive_of_exactFirstMissing
    (b : S1725TorsionBasis S1987Five)
    (h : S2203ExactFirstMissing b) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses b h.1 h.2

end LeanFormal.IUT.XiFPaper.S2203D5RangeActual

end
