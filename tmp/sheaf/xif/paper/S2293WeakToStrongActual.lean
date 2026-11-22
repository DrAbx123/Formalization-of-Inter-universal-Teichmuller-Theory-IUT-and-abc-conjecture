import tmp.sheaf.xif.paper.S2290StrongCospanActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2293: weak-to-strong upgrade audit

`StrongEtaleStackFiniteEtaleMorphism` adds to `EtaleStackFiniteEtaleMorphism`
the full cone essential-surjectivity of the chosen base-change presentations
(via `StrongEtaleStackBaseChangePresentation`).  Upgrading an arbitrary weak
structure requires producing, at every test point, a full presentation; this
is exactly the S1852/S2100 full 2-universal property, unavailable for an
arbitrary `g.map`.  No upgrade or counterexample is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2293WeakToStrongActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2290StrongCospanActual

universe u

/-- The audited upgrade. -/
def S2293Upgrade : Type 1 :=
  S2290WeakToStrongUpgrade

#check StrongEtaleStackFiniteEtaleMorphism
#check StrongEtaleStackFiniteEtaleMorphism.toWeak
#check StrongEtaleStackBaseChangePresentation
#check S2293Upgrade

end LeanFormal.IUT.XiFPaper.S2293WeakToStrongActual

end
