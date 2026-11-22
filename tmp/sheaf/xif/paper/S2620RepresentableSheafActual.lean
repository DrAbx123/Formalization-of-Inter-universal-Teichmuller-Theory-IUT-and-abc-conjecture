import tmp.sheaf.xif.paper.S2619ActionGroupoidFiberSkeleton
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2620RepresentableSheafActual

universe u
variable (F : Type u) [Field F]

theorem S2620_representableHom_isSheaf_global
    (X : Iut.SchemeOverField F) :
    Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology F)
      (yoneda.obj X) :=
  LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed.representableEtalePresheaf_isSheaf F X

abbrev S2620Slice (S : Iut.SchemeOverField F) :=
  (Iut.SchemeOverField.etaleTopology F).over S

theorem S2620_representableHom_slice_isSheaf
    (X S : Iut.SchemeOverField F) :
    Presheaf.IsSheaf (S2620Slice (F := F) S)
      ((Over.forget S).op ⋙ yoneda.obj X) :=
  (Over.forget S).op_comp_isSheaf_of_isSheaf
    (J := (Iut.SchemeOverField.etaleTopology F).over S)
    (K := Iut.SchemeOverField.etaleTopology F)
    (P := yoneda.obj X)
    (S2620_representableHom_isSheaf_global F X)

def S2620_representableHom_sheaf_goal
    (X S : Iut.SchemeOverField F) : Prop :=
  Presheaf.IsSheaf (S2620Slice (F := F) S)
    ((Over.forget S).op ⋙ yoneda.obj X)

#check S2620_representableHom_isSheaf_global
#check S2620_representableHom_sheaf_goal
#print axioms S2620_representableHom_isSheaf_global

end LeanFormal.IUT.XiFPaper.S2620RepresentableSheafActual
end