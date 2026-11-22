import tmp.sheaf.xif.paper.S2261BigSquareEssSurjActual
import tmp.sheaf.xif.paper.S2095BigLiftUniqActual
import tmp.sheaf.xif.paper.S2101SiteNaturalityActual

/-! # S2262: audit of S2095BigLiftUniq

`S2095BigLiftUniq` asks, for every cone `c`, every `h` with projection
isomorphisms `h ; toA ≅ c.toX` and `h ; toB ≅ c.toY`, an isomorphism
`h ≅ S2076Witness.lift c`.  The tree's only route needs the projection
compatibility `S2096ProjectionCompatibility` plus site naturality of
`S1893LiftIsoOfConeIso`; S2101 proves the latter *given* compatibility.

The compatibility is not derivable for arbitrary `h` from the weak witness
(S2099/S2104 isolate it; S2104 only supplies the canonical case).  Hence the
exact first missing is arbitrary-h projection compatibility/site naturality.
No proof or refutation is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2262BigLiftUniqActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2261BigSquareEssSurjActual

universe u

def S2262LiftUniqueness : Prop :=
  S2095BigLiftUniq

#check S2262LiftUniqueness
#check S2096LiftUniq_of_projectionCompat
#check S2095BigEssSurj_of_liftUniq

end LeanFormal.IUT.XiFPaper.S2262BigLiftUniqActual

end
