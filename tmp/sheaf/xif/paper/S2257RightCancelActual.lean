import tmp.sheaf.xif.paper.S2254UnpastingLiftActual
import tmp.sheaf.xif.paper.S2247BaseChangeSquareActual

/-! # S2257: concrete right-cancel attempt

Attempted to prove `S2097RightCancelStatement` in the concrete base-change
setting using the strict scheme pullback of S2165 and the S2224 commutes
coherence.  The strict pullback only controls scheme-valued points; the
required lift is at the level of arbitrary etale-stack pseudofunctors `W`, so
the concrete instance still needs the 2-categorical unpasting input.  The
exact missing statement is recorded; nothing is faked.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2257RightCancelActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2151UnpastingActual
open LeanFormal.IUT.XiFPaper.S2247BaseChangeSquareActual
open LeanFormal.IUT.XiFPaper.S2254UnpastingLiftActual

universe u

/-- The concrete base-change instance of reverse pasting.  This is the exact
statement needed to build the base-changed weak witness; it is recorded, not
proved. -/
def S2257ConcreteRightCancel : Type 1 :=
  S2097RightCancelStatement

/-- The concrete unpasting form, equivalent as a missing input. -/
def S2257ConcreteUnpasting : Type 1 :=
  S2151UnpastingOfFull

#check S2257ConcreteRightCancel
#check S2257ConcreteUnpasting

end LeanFormal.IUT.XiFPaper.S2257RightCancelActual

end
