import tmp.sheaf.xif.paper.S2095BigLiftUniqActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2102: the g-presentation square needs the full 2-universal property

`S1852ConeEssSurj P` is definitionally `S1827EssSurjOf (S1852WeakSquare P)
`P.isPullback`.  Thus for the presentations `Pg` used in S2086, the exact
missing input is the full 2-universal property of the presentation square,
not derivable from the weak `isPullback` field alone (cf. S1899).

No inhabitant is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2102GPresentationFullActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

universe u

variable {source target : EtaleStackOverField S1726K} {map : source.Hom target}
variable {testScheme : SchemeOverField S1726K}
variable {point : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber}

/-- `S1852ConeEssSurj P` is the full `S1827EssSurjOf` of the weak square. -/
theorem S2102ConeEssSurj_iff (P : EtaleStackBaseChangePresentation map testScheme point) :
    S1852ConeEssSurj P ↔
      S1827EssSurjOf (S1852WeakSquare P) P.isPullback :=
  Iff.rfl

/-- Exact missing full property for every g-presentation used in S2086. -/
def S2102GPresentationFull : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
    S1852ConeEssSurj Pg

#check S2102ConeEssSurj_iff
#check S2102GPresentationFull

end LeanFormal.IUT.XiFPaper.S2102GPresentationFullActual

end
