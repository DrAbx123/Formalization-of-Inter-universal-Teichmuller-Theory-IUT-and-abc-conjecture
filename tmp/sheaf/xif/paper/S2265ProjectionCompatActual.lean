import tmp.sheaf.xif.paper.S2262BigLiftUniqActual
import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual
import tmp.sheaf.xif.paper.S2095BigLiftUniqActual
import tmp.sheaf.xif.paper.S2104ButterflyTwistActual
import tmp.sheaf.xif.paper.S2101SiteNaturalityActual
import tmp.sheaf.xif.paper.S1836CoverPullbackStackActual
import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual
import tmp.sheaf.xif.paper.S2099BigSquareEssSurjActual

/-! # S2265: arbitrary-h projection compatibility audit

`S2096ProjectionCompatibility c h eX eY` is the twist equation for a pair of
projection isomorphisms.  S2104 proves it only for the **canonical** lift
`h = S2076Witness.lift c`, `eX = liftToX`, `eY = liftToY` (via
`S2099TwistAt_canonical`).  For arbitrary `h` with projection isomorphisms the
structure 2-cell of `h` is independent of the canonical one; the twist pins it
to the canonical value and is not implied by the weak seven fields.

We record the arbitrary-h statement as a missing Type.  No proof or formal
counterexample is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2265ProjectionCompatActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2262BigLiftUniqActual

universe u

#check S2095BigLiftUniq
#check S2094BigSquareEssSurj

end LeanFormal.IUT.XiFPaper.S2265ProjectionCompatActual

end
