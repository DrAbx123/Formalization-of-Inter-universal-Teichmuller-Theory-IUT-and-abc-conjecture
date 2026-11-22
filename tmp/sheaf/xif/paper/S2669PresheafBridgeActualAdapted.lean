import tmp.sheaf.xif.paper.S2668FiberCoherenceActual
import tmp.sheaf.xif.paper.S2669TorsorPresheaf0Actual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2669PresheafBridgeActualAdapted

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2669TorsorPresheaf0Actual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2619ActionGroupoidData (l := l) (F := F))

theorem S2669PresheafHom_eq (S : Iut.SchemeOverField F)
    (M N : @CategoryTheory.ActionCategory (S2619G l) (inferInstance)
      (S2619Hom (l := l) (F := F) D (Opposite.op S))
      (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S))) :
    (S2668FiberPseudofunctor (l := l) (F := F) D).presheafHom
      (M : (S2668FiberPseudofunctor (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S)))
      (N : (S2668FiberPseudofunctor (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S))) =
      S2669TorsorPresheaf0 (l := l) (F := F) D S
        (@CategoryTheory.ActionCategory.back (S2619G l) (inferInstance)
          (S2619Hom (l := l) (F := F) D (Opposite.op S))
          (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S)) M)
        (@CategoryTheory.ActionCategory.back (S2619G l) (inferInstance)
          (S2619Hom (l := l) (F := F) D (Opposite.op S))
          (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S)) N) := by
  apply CategoryTheory.Functor.ext
  · intro a b f
    ext g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro Y
    rfl

#check S2669PresheafHom_eq
#print axioms S2669PresheafHom_eq
end LeanFormal.IUT.XiFPaper.S2669PresheafBridgeActualAdapted
end
