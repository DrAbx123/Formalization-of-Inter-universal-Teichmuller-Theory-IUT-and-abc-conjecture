import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual

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
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1758LiftIsoProbeAdapted

variable {A B : S1728Cover}

noncomputable def S1758LiftIso {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    S1755Lift A B f ≅ S1755Lift A B g where
  hom := S1757LiftHom e
  inv := S1757LiftHom e.symm
  hom_inv_id := by
    apply (S1755BaseChange B).isPullback.twoCell_ext
    · change CategoryTheory.Bicategory.whiskerRight
        (S1757LiftHom e ≫ S1757LiftHom e.symm) (S1755BaseChange B).toSource =
        CategoryTheory.Bicategory.whiskerRight (𝟙 (S1755Lift A B f))
          (S1755BaseChange B).toSource
      rw [CategoryTheory.Bicategory.comp_whiskerRight, CategoryTheory.Bicategory.id_whiskerRight]
    · change CategoryTheory.Bicategory.whiskerRight
        (S1757LiftHom e ≫ S1757LiftHom e.symm)
          (S1755BaseChange B).projectionMap.transformation =
        CategoryTheory.Bicategory.whiskerRight (𝟙 (S1755Lift A B f))
          (S1755BaseChange B).projectionMap.transformation
      rw [CategoryTheory.Bicategory.comp_whiskerRight, CategoryTheory.Bicategory.id_whiskerRight]

#print axioms S1758LiftIso

end LeanFormal.IUT.XiFPaper.S1758LiftIsoProbeAdapted
end
