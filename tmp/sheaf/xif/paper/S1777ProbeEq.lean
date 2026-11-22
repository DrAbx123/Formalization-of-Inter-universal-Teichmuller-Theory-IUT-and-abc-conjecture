import Mathlib.RingTheory.Etale.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Gen3

#check @eqToHom_map
#check @Functor.map_eqToHom
#check @CategoryTheory.eqToHom_comp_iff
#check @eqToHom_trans
#check @eqToHom_refl
#check @CategoryTheory.eqToIso_hom
#check @CategoryTheory.eqToIso_inv
#check @CategoryTheory.eqToHom_comp_heq
#check @heq_eq_eq

variable {C : Type} [Category C] {X Y : C} (h : X = Y) (f : X ⟶ X)

example : eqToHom h ≫ eqToHom h.symm = 𝟙 X := by simp
example : eqToHom h.symm ≫ eqToHom h = 𝟙 Y := by simp

end Gen3
