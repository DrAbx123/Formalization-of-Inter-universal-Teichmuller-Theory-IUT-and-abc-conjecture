import tmp.sheaf.xif.paper.S1761SubsingletonIsoActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1762OverModelHomActual

variable {A B : S1728Cover}

/-- An over-base model morphism: a scheme morphism of the base-change
models whose 2-Yoneda strong transformation commutes with the structure
projections to the affine base. -/
structure S1762ModelHomOver (A B : S1728Cover) where
  hom : S1733Model A ⟶ S1733Model B
  overBase : Nonempty (Iso
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) hom)
      (S1755BaseChange B).projectionMap.transformation)
    (S1755BaseChange A).projectionMap.transformation)

/-- The forward map to be constructed: every cover-map 2-iso class gives an
over-base model morphism. -/
def S1762QuotToOverTarget : Prop :=
  forall A B : S1728Cover,
    Nonempty (S1756CoverMapQuot A B -> S1762ModelHomOver A B)

/-- The inverse map: every over-base model morphism comes from a cover-map
2-iso class. -/
def S1762OverToQuotTarget : Prop :=
  forall A B : S1728Cover,
    Nonempty (S1762ModelHomOver A B -> S1756CoverMapQuot A B)

/-- The corrected quotient equivalence target. -/
def S1762OverEquivTarget : Prop :=
  forall A B : S1728Cover,
    Nonempty (S1756CoverMapQuot A B ≃ S1762ModelHomOver A B)

#check S1762OverEquivTarget

end LeanFormal.IUT.XiFPaper.S1762OverModelHomActual
end
