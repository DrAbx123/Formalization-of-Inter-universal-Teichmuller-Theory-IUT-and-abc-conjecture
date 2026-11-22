import Mathlib.RingTheory.Etale.Pi

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2527ProductEtaleActual

universe u
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

abbrev Fam (A B : Type u) : Bool → Type u := fun b => Bool.rec B A b

instance (b : Bool) : CommRing (Fam A B b) := Bool.rec inferInstance inferInstance b
instance (b : Bool) : Algebra R (Fam A B b) := Bool.rec inferInstance inferInstance b
instance [Algebra.Etale R A] [Algebra.Etale R B] (b : Bool) :
    Algebra.Etale R (Fam A B b) := Bool.rec inferInstance inferInstance b

noncomputable def prodPiAlgEquiv : (A × B) ≃ₐ[R] (∀ b : Bool, Fam A B b) where
  toFun p := fun b => match b with | true => p.1 | false => p.2
  invFun f := (f true, f false)
  left_inv p := by cases p; rfl
  right_inv f := by funext b; cases b <;> rfl
  map_add' p q := by funext b; cases b <;> rfl
  map_mul' p q := by funext b; cases b <;> rfl
  commutes' r := by funext b; cases b <;> rfl

theorem S2527_prod_etale [Algebra.Etale R A] [Algebra.Etale R B] :
    Algebra.Etale R (A × B) := by
  exact Algebra.Etale.of_equiv (prodPiAlgEquiv R A B).symm

#print axioms S2527_prod_etale

end LeanFormal.IUT.XiFPaper.S2527ProductEtaleActual
end