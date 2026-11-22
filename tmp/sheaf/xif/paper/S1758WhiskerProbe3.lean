import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual

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

namespace LeanFormal.IUT.XiFPaper.S1758WhiskerProbe3

variable {A B : S1728Cover}

noncomputable abbrev S1758Square (B : S1728Cover) :
    EtalePseudofunctorSquare (S1755ModelStack B) (S1755Source B)
      (S1755Y S1726AffineOver) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S1755BaseChange B).toSource
    (S1755BaseChange B).projectionMap.transformation B.map S1733BasePoint
    (S1755BaseChange B).commutes

noncomputable def S1758Witness (B : S1728Cover) :
    (S1758Square B).TwoPullbackWitness := (S1755BaseChange B).isPullback

noncomputable abbrev S1758Cone (f : S1728CoverMap A B) :
    (S1758Square B).Cone (S1755ModelStack A) := S1755Cone A B f

noncomputable def S1758ConeMorphism {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    (S1758Square B).ConeMorphism (S1758Cone f) (S1758Cone g) where
  toX := by
    change Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource f.map ⟶
      Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource g.map
    exact Pseudofunctor.StrongTrans.whiskerLeft (S1755BaseChange A).toSource e.hom
  toY := 𝟙 ((S1755BaseChange A).projectionMap.transformation)
  compatibility := by
    haveI : Subsingleton
        (Pseudofunctor.StrongTrans.vcomp (S1758Cone f).toX (S1758Square B).xToBase ⟶
          Pseudofunctor.StrongTrans.vcomp (S1758Cone g).toY (S1758Square B).yToBase) := by
      apply S1800Modification_subsingleton
    exact Subsingleton.elim _ _
noncomputable abbrev S1758LiftW (f : S1728CoverMap A B) :
    S1755ModelStack A ⟶ S1755ModelStack B :=
  (S1758Witness B).lift (S1755ModelStack A) (S1758Cone f)

noncomputable def S1758LiftHomW {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) : S1758LiftW (B := B) f ⟶ S1758LiftW (B := B) g :=
  (S1758Witness B).liftTwoCell (S1755ModelStack A)
    (S1758Cone f) (S1758Cone g) (S1758ConeMorphism e)

theorem S1758Whisker {f g : S1728CoverMap A B} (e : f.map ≅ g.map) :
    CategoryTheory.Bicategory.whiskerRight (a := S1755ModelStack A) (b := S1755ModelStack B) (c := S1755Source B)
      (S1758LiftHomW e ≫ S1758LiftHomW e.symm :
        S1758LiftW (B := B) f ⟶ S1758LiftW (B := B) f)
      (S1755BaseChange B).toSource =
    CategoryTheory.Bicategory.whiskerRight (a := S1755ModelStack A) (b := S1755ModelStack B) (c := S1755Source B)
      (𝟙 (S1758LiftW (B := B) f) : S1758LiftW (B := B) f ⟶ S1758LiftW (B := B) f)
        (S1755BaseChange B).toSource := by
  rw [CategoryTheory.Bicategory.comp_whiskerRight]
  simp only [S1758LiftHomW]
  rw [← show (S1758Square B).toX = (S1755BaseChange B).toSource from rfl]
  rw [(S1758Witness B).liftTwoCell_toX, (S1758Witness B).liftTwoCell_toX]
  rw [CategoryTheory.Bicategory.id_whiskerRight (S1758LiftW (B := B) f) (S1755BaseChange B).toSource]
  simp only [S1758Witness, S1757ConeMorphism, CategoryTheory.Bicategory.whiskerLeft_comp,
    CategoryTheory.Bicategory.whiskerLeft_id, Iso.inv_hom_id, Iso.hom_inv_id,
    Category.assoc, Category.comp_id, Category.id_comp]

#print axioms S1758Whisker

end LeanFormal.IUT.XiFPaper.S1758WhiskerProbe3
end
