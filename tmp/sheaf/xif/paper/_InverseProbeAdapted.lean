import Mathlib
open CategoryTheory
namespace P
example {A B C : Type} [Category A] [Category B] [Category C]
    (h1 : A = B) (h2 : B = C) :
    (eqToHom h1 ≫ eqToHom h2) ≫ (eqToHom h2.symm ≫ eqToHom h1.symm) = 𝟙 A := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp]
end P
