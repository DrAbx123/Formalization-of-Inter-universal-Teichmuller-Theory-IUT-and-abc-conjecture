import tmp.sheaf.xif.paper.S2621TorsorPresheafActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2669TorsorPresheaf0Actual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2619ActionGroupoidData (l := l) (F := F))

noncomputable def S2669TorsorPresheaf0 (S : Iut.SchemeOverField F)
    (M N : S2619Hom (l := l) (F := F) D (Opposite.op S)) :
    (Over S)ᵒᵖ ⥤ Type :=
  { obj T :=
      { g : ZMod l.value //
        (T.unop.hom ≫ M) ≫ ((D.rho g).hom) = T.unop.hom ≫ N }
    map {T T'} f :=
      ↾fun g => ⟨g.1, by
        have h := g.2
        rw [show (Opposite.unop T').hom =
            f.unop.left ≫ (Opposite.unop T).hom from (Over.w f.unop).symm]
        simpa only [Category.assoc] using
          congrArg (fun x => f.unop.left ≫ x) h⟩
    map_id T := by
      ext g
      rfl
    map_comp f g := by
      ext h
      rfl }

#check S2669TorsorPresheaf0
end LeanFormal.IUT.XiFPaper.S2669TorsorPresheaf0Actual
end
