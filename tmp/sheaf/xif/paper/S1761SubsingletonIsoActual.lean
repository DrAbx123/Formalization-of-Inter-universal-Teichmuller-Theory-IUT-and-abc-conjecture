import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual
import tmp.sheaf.xif.paper.S1756QuotientActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual

variable {A B : S1728Cover}

/-- 2-cells between lifts are modifications into the representable model
stack, hence subsingletons; this gives the Iso of lifts directly. -/
noncomputable def S1761LiftIso {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) : S1755Lift A B f ≅ S1755Lift A B g where
  hom := S1757LiftHom e
  inv := S1757LiftHom e.symm
  hom_inv_id := by
    haveI : Subsingleton (S1755Lift A B f ⟶ S1755Lift A B f) := by
      apply S1800Modification_subsingleton
    exact Subsingleton.elim _ _
  inv_hom_id := by
    haveI : Subsingleton (S1755Lift A B g ⟶ S1755Lift A B g) := by
      apply S1800Modification_subsingleton
    exact Subsingleton.elim _ _

/-- The missing functoriality is now unconditional. -/
theorem S1761LiftFunctoriality : S1757LiftFunctoriality := by
  intro A B f g hr
  obtain ⟨e⟩ := hr
  exact ⟨S1761LiftIso e⟩

/-- Quotient extraction is well defined. -/
theorem S1761LiftWellDefined : S1756LiftWellDefined :=
  S1756LiftWellDefined_of_functoriality S1761LiftFunctoriality

/-- Unconditional descended quotient extraction. -/
noncomputable def S1761QuotToModel (A B : S1728Cover) :
    S1756CoverMapQuot A B -> (S1733Model A ⟶ S1733Model B) :=
  S1756QuotToModel S1761LiftWellDefined A B

/-- Unconditional injectivity on the quotient. -/
theorem S1761QuotToModel_injective (A B : S1728Cover) :
    Function.Injective (S1761QuotToModel A B) :=
  S1756QuotToModel_injective S1761LiftWellDefined A B

#print axioms S1761LiftFunctoriality
#print axioms S1761QuotToModel_injective
#print axioms S1761LiftWellDefined

end LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual
end
