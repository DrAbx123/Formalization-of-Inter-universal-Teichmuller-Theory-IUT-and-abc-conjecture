import tmp.sheaf.xif.paper.S2668FiberCoherenceActual
import tmp.sheaf.xif.paper.S2669TorsorPresheaf0Actual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2669PresheafHomIsoActualAdapted

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2669TorsorPresheaf0Actual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2619ActionGroupoidData (l := l) (F := F))

noncomputable def S2669PresheafHomIso (S : Iut.SchemeOverField F)
    (M N : @CategoryTheory.ActionCategory (S2619G l) (inferInstance)
      (S2619Hom (l := l) (F := F) D (Opposite.op S))
      (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S))) :
    ((S2668FiberPseudofunctor (l := l) (F := F) D).presheafHom
      (M : (S2668FiberPseudofunctor (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S)))
      (N : (S2668FiberPseudofunctor (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S))))
    ≅ S2669TorsorPresheaf0 (l := l) (F := F) D S
        (@CategoryTheory.ActionCategory.back (S2619G l) (inferInstance)
          (S2619Hom (l := l) (F := F) D (Opposite.op S))
          (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S)) M)
        (@CategoryTheory.ActionCategory.back (S2619G l) (inferInstance)
          (S2619Hom (l := l) (F := F) D (Opposite.op S))
          (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S)) N) := by
  let Fp : (Over S)ᵒᵖ ⥤ Type :=
    (S2668FiberPseudofunctor (l := l) (F := F) D).presheafHom
      (M : (S2668FiberPseudofunctor (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S)))
      (N : (S2668FiberPseudofunctor (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S)))
  let Gp : (Over S)ᵒᵖ ⥤ Type :=
    S2669TorsorPresheaf0 (l := l) (F := F) D S
      (@CategoryTheory.ActionCategory.back (S2619G l) (inferInstance)
        (S2619Hom (l := l) (F := F) D (Opposite.op S))
        (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S)) M)
      (@CategoryTheory.ActionCategory.back (S2619G l) (inferInstance)
        (S2619Hom (l := l) (F := F) D (Opposite.op S))
        (S2619MulAction (l := l) (F := F) (D := D) (Opposite.op S)) N)
  change Fp ≅ Gp
  exact NatIso.ofComponents
    (fun T => Iso.refl (Fp.obj T))
    (by
      intro T T' f
      ext g
      change (Fp.map f) g = (Gp.map f) g
      apply Subtype.ext
      dsimp [Fp, Gp]
      simp only [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
        S2669TorsorPresheaf0, S2668FiberPseudofunctor, S2668FiberFunctor,
        Functor.toPseudofunctor'_map, Functor.toPseudofunctor'_mapComp,
        Functor.toPseudofunctor'_mapId]
      rfl)

#check S2669PresheafHomIso
#print axioms S2669PresheafHomIso
end LeanFormal.IUT.XiFPaper.S2669PresheafHomIsoActualAdapted
end
