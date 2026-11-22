import tmp.sheaf.xif.paper.S2620RepresentableSheafActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2619ActionGroupoidData l F)

abbrev S2621Hom (S : Iut.SchemeOverField F) : Type u := S ⟶ D.U

noncomputable def S2620TorsorPresheaf
    (S : Iut.SchemeOverField F)
    (M N : S2621Hom (F := F) D S) :
    (Over S)ᵒᵖ ⥤ Type (u+1) where
  obj T :=
    ULift.{u+1,0} { g : ZMod l.value //
      (T.unop.hom ≫ M) ≫ ((D.rho g).hom) = T.unop.hom ≫ N }
  map {T T'} f :=
    ↾fun g => ⟨g.down.val, by
      have h := g.down.property
      rw [show (Opposite.unop T').hom =
          f.unop.left ≫ (Opposite.unop T).hom from (Over.w f.unop).symm]
      simpa only [Category.assoc] using
        congrArg (fun x => f.unop.left ≫ x) h⟩
  map_id T := by
    ext g
    rfl
  map_comp f g := by
    ext h
    rfl

#check S2620TorsorPresheaf

end LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
end