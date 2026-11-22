import tmp.sheaf.xif.paper.S2523MapHomEqActual
import tmp.sheaf.xif.paper.S2519ForwardFunctorPartialActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2519ForwardFunctorPartialActual
open LeanFormal.IUT.XiFPaper.S2523MapHomEqActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2519ForwardFunctorActualMap

/-- Unconditional map on quotient homs, using S2523 well-definedness. -/
noncomputable def S2519ForwardQuotMapActual
    {C D : S2519SourceCategory}
    (f : S1728CoverMapClass (A := C) (B := D)) :
    S2519ForwardObj C ⟶ S2519ForwardObj D :=
  S2519ForwardQuotMap S2523ForwardMapWellDefined f

/-- The functor with unconditional map and explicit law hypotheses. -/
noncomputable def S2519ForwardFunctorActualMap
    (hid : ∀ C : S2519SourceCategory,
      S2519ForwardQuotMapActual (𝟙 C) = 𝟙 (S2519ForwardObj C))
    (hcomp : ∀ {A B C : S2519SourceCategory}
      (f : S1728CoverMapClass (A := A) (B := B))
      (g : S1728CoverMapClass (A := B) (B := C)),
      S2519ForwardQuotMapActual (S1728CoverMapClassComp f g) =
        S2519ForwardQuotMapActual f ≫ S2519ForwardQuotMapActual g) :
    S2519SourceCategory ⥤ FiniteEtaleCover S2482AffineScheme :=
  S2519ForwardFunctor S2523ForwardMapWellDefined hid hcomp

#check S2519ForwardQuotMapActual
#check S2519ForwardFunctorActualMap
#print axioms S2519ForwardQuotMapActual

end LeanFormal.IUT.XiFPaper.S2519ForwardFunctorActualMap
end
