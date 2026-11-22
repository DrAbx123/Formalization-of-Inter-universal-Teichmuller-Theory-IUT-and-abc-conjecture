import tmp.sheaf.xif.paper.S2086ToAAssemblyActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2094: the two full-2-universal inputs for S2086BaseChangePullback

S2086BaseChangePullback cannot be derived from the weak S2076 witness plus
S2071 pasting.  The butterfly pasting needs:

1. `S2094BigSquareEssSurj`: the iso-comma square (toA, toB, f.map, g.map) has
   the full 2-universal property `S1827EssSurjOf`, not only a weak witness;
2. `S2094GPresentationConeEssSurj`: every used g-presentation has the full
   cone essential-surjectivity `S1852ConeEssSurj`.

Both are stated here as Prop; no inhabitant is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual

universe u

/-- Full 2-universal property of the iso-comma square. -/
def S2094BigSquareEssSurj : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    S1827EssSurjOf
      (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map (commutes f g))
      (S2076Witness (f := f) (g := g))

/-- Full cone essential surjectivity of every g-presentation used in S2086. -/
def S2094GPresentationConeEssSurj : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
    S1852ConeEssSurj Pg

#check S2094BigSquareEssSurj
#check S2094GPresentationConeEssSurj

end LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

end
