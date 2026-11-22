import tmp.sheaf.xif.paper.S2811IsPrestackActual

noncomputable section
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2811P2ActualAdapted

universe u

variable (F : Type u) [Field F]
variable (X S : Iut.SchemeOverField F) (m n : S ⟶ X)

abbrev PObj (m n : S ⟶ X) (T : (Over S)ᵒᵖ) : Type u :=
  ULift.{u} (Subtype (fun _ : Unit => T.unop.hom ≫ m = T.unop.hom ≫ n))

noncomputable def P (m n : S ⟶ X) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := PObj (F := F) (X := X) (S := S) m n T
  map {T₁ T₂} q := fun x => ULift.up (⟨(), by
      have hw : q.unop.left ≫ T₁.unop.hom = T₂.unop.hom := q.unop.w
      have hx : T₁.unop.hom ≫ m = T₁.unop.hom ≫ n := x.down.2
      calc
        T₂.unop.hom ≫ m = (q.unop.left ≫ T₁.unop.hom) ≫ m := by rw [hw]
        _ = q.unop.left ≫ (T₁.unop.hom ≫ m) := by simp [Category.assoc]
        _ = q.unop.left ≫ (T₁.unop.hom ≫ n) := by rw [hx]
        _ = (q.unop.left ≫ T₁.unop.hom) ≫ n := by simp [Category.assoc]
        _ = T₂.unop.hom ≫ n := by rw [hw]⟩)
  map_id T := by
    ext x
  map_comp q r := by
    ext x

instance P_subsingleton (m n : S ⟶ X) (T : (Over S)ᵒᵖ) :
    Subsingleton ((P F X S m n).obj T) :=
  ⟨fun a b => ULift.ext _ _ (Subtype.ext (Subsingleton.elim a.down.1 b.down.1))⟩

#check P
#check P_subsingleton
#print axioms P

end LeanFormal.IUT.XiFPaper.S2811P2ActualAdapted
end
