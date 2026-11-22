import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual
open CategoryTheory

/-!
  Mainline: Order(E) category laws (hom subsingleton, identity/composition normal forms).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCatLawsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u



theorem orderCat_id_eq (E : Type u) [Preorder E] (X : OrderCat E) :
    (𝟙 X : X ⟶ X) = PLift.up (le_refl X) :=
  rfl

theorem orderCat_comp_eq (E : Type u) [Preorder E] {X Y Z : OrderCat E}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = PLift.up (le_trans f.down g.down) :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCatLawsActual