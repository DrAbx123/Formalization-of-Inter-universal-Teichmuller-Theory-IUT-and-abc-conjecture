import tmp.sheaf.xif.paper.S2100GPresentationConeEssSurjActual
import tmp.sheaf.xif.paper.S2095BigLiftUniqActual
import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual

/-! # S2261: audit of S2094BigSquareEssSurj

Audit conclusions:
* `S2100NotGPresentationConeEssSurj` refutes only
  `S2094GPresentationConeEssSurj`, not `S2094BigSquareEssSurj`;
* no counterexample to `S2094BigSquareEssSurj` is known in the tree;
* the only reduction available is `S2095BigLiftUniq ->
  S2094BigSquareEssSurj`, and `S2095BigLiftUniq` itself is not proved.

Hence `S2094BigSquareEssSurj` remains unverified; the exact first missing is
the site-level lift-uniqueness/naturality of S2095BigLiftUniq.  No proof or
refutation is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2261BigSquareEssSurjActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual
open LeanFormal.IUT.XiFPaper.S2100GPresentationConeEssSurjActual

universe u

/-- The audited target. -/
def S2261BigSquareEssSurj : Prop :=
  S2094BigSquareEssSurj

/-- The exact missing site-level lift uniqueness. -/
def S2261LiftUniqueness : Prop :=
  S2095BigLiftUniq

#check S2261BigSquareEssSurj
#check S2261LiftUniqueness
#check S2100NotGPresentationConeEssSurj
#check S2095BigEssSurj_of_liftUniq

end LeanFormal.IUT.XiFPaper.S2261BigSquareEssSurjActual

end
