import tmp.sheaf.xif.paper.S2265ProjectionCompatActual
import tmp.sheaf.xif.paper.S2104ButterflyTwistActual
import tmp.sheaf.xif.paper.S2101SiteNaturalityActual

/-! # S2272: arbitrary-h compatibility -- audit

Using S2104's canonical-lift compatibility plus S2101 uniqueness only proves
the compatibility for the canonical lift itself, not for an arbitrary `h` with
arbitrary projection isomorphisms.  The missing premise is exactly that `h`
and its projection isomorphisms are the canonical ones, which is the
arbitrary-h compatibility being sought.  No proof or formal counterexample is
produced here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2272ArbitraryHCompatActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2265ProjectionCompatActual

universe u

#check S2095BigLiftUniq
#check S2094BigSquareEssSurj
#check S2096LiftUniq_of_projectionCompat
#check S2099TwistAt_canonical

end LeanFormal.IUT.XiFPaper.S2272ArbitraryHCompatActual

end
