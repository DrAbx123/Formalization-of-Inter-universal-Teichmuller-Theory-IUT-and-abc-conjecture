import tmp.sheaf.xif.paper.S2811IsPrestackActual

noncomputable section
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2811IsPrestackActual

universe u

variable (F : Type u) [Field F]
variable (X S : Iut.SchemeOverField F) (m n : S ⟶ X)

/-- The subterminal presheaf on `Over S` of points where `m` and `n` agree. -/
noncomputable def S2811P (m n : S ⟶ X) : (Over S)ᵒᵖ ⥤ Type u where
  obj T :=
    ULift.{u} (Subtype (fun _ : Unit => T.unop.hom ≫ m = T.unop.hom ≫ n))
  map {T₁ T₂} q :
      (S2811P m n).obj T₁ → (S2811P m n).obj T₂ := fun x =>
    (ULift.up (⟨(), by
      have hw : q.unop.left ≫ T₁.unop.hom = T₂.unop.hom := q.unop.w
      calc
        T₂.unop.hom ≫ m = (q.unop.left ≫ T₁.unop.hom) ≫ m := by rw [hw]
        _ = q.unop.left ≫ (T₁.unop.hom ≫ m) := by simp [Category.assoc]
        _ = q.unop.left ≫ (T₁.unop.hom ≫ n) := by rw [x.2]
        _ = (q.unop.left ≫ T₁.unop.hom) ≫ n := by simp [Category.assoc]
        _ = T₂.unop.hom ≫ n := by rw [hw]⟩ : Subtype (fun _ : Unit => T₂.unop.hom ≫ m = T₂.unop.hom ≫ n)))
  map_id T := by
    ext x
  map_comp q r := by
    ext x

instance S2811P_subsingleton (m n : S ⟶ X) (T : (Over S)ᵒᵖ) :
    Subsingleton ((S2811P F X S m n).obj T) :=
  ⟨fun a b => ULift.ext _ _ (Subtype.ext (Subsingleton.elim a.1.1 b.1.1))⟩

#check S2811P
#check S2811P_subsingleton
#print axioms S2811P

end LeanFormal.IUT.XiFPaper.S2811IsPrestackActual
end
