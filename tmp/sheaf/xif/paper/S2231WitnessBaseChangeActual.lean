import tmp.sheaf.xif.paper.S2224BaseChangeCommutesFinalActual
import tmp.sheaf.xif.paper.S2096StackMorphismActual

/-! # S2231: witness base change -- exact missing interface

The base-changed presentation data (apex, projections, toSource, commutes)
are actual in S2165/S2175/S2224.  The remaining step is the weak
`TwoPullbackWitness` transport along the finite-etale square; no map producing
it from `Q.isPullback` is available, so the missing input is recorded as the
base-change statement itself.  No witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2231WitnessBaseChangeActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual

universe u

/-- Exact missing witness transport: a presentation base-changed along
finite-etale `s`, with finite-etale projection. -/
def S2231WitnessTransport : Type 1 :=
  S2096BaseChangeStatement

#check S2231WitnessTransport
#check S2096BaseChangeStatement

end LeanFormal.IUT.XiFPaper.S2231WitnessBaseChangeActual

end
