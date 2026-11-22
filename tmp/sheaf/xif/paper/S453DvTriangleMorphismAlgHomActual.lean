import tmp.sheaf.xif.paper.S432SmallModelActual
import tmp.sheaf.xif.paper.S446Example32DivisorNaturalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S453DvTriangleMorphismAlgHomActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S446Example32DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual

universe u
variable (K : Type u) [Field K]

noncomputable abbrev coverField (X : Example32SmallBase K) : Type u :=
  (ULiftHom.objDown X).unop.obj.obj

noncomputable def arrowAlgebraMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    coverField K Y →ₐ[K] coverField K X :=
  (f.down.unop).hom.hom.hom

theorem arrowAlgebraMap_id (X : Example32SmallBase K) :
    arrowAlgebraMap K (𝟙 X) = AlgHom.id K (coverField K X) := by
  ext x
  rfl

theorem arrowAlgebraMap_comp {X Y Z : Example32SmallBase K}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    arrowAlgebraMap K (f ≫ g) =
      (arrowAlgebraMap K f).comp (arrowAlgebraMap K g) := by
  ext x
  rfl

structure DvSmallMorphismToAlgHomBridge
    (K : Type u) [Field K] where
  toAlgHom : ∀ {X Y : Example32SmallBase K},
    (X ⟶ Y) → coverField K Y →ₐ[K] coverField K X
  id_law : ∀ X : Example32SmallBase K,
    toAlgHom (𝟙 X) = AlgHom.id K (coverField K X)
  comp_law : ∀ {X Y Z : Example32SmallBase K}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    toAlgHom (f ≫ g) = (toAlgHom f).comp (toAlgHom g)

noncomputable def dvSmallMorphismToAlgHomBridge :
    DvSmallMorphismToAlgHomBridge K where
  toAlgHom := arrowAlgebraMap K
  id_law := arrowAlgebraMap_id K
  comp_law := arrowAlgebraMap_comp K

def DvTriangleCovariantBridgeExactGap : Prop :=
  Nonempty (DvTriangleCategoryMorphismToAlgHomBridge K)

end LeanFormal.IUT.XiFPaper.S453DvTriangleMorphismAlgHomActual

end
