import tmp.sheaf.xif.paper.S2272ArbitraryHCompatActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual

/-! # S2274: attempted counterexample for arbitrary-h compatibility

No formal counterexample was obtained.  The available noncanonical data
(`S1850Doubled`, `inl != inr`, `S1827EssSurjNotFromWitness`) are 1-cell /
full-essential-surjectivity failures, not a failure of the 2-cell twist
`S2096ProjectionCompatibility` for a specific `h` with projection
isomorphisms.  Constructing the latter requires a cone with a nontrivial
automorphism of its projections that the twist does not absorb; no such
concrete cone is built in the tree.

Status: unrefuted; exact first missing remains arbitrary-h compatibility.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2274ArbitraryHCounterexampleActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual
open LeanFormal.IUT.XiFPaper.S2272ArbitraryHCompatActual

universe u

#check S1827EssSurjNotFromWitness
#check S2095BigLiftUniq
#check S2094BigSquareEssSurj

end LeanFormal.IUT.XiFPaper.S2274ArbitraryHCounterexampleActual

end
