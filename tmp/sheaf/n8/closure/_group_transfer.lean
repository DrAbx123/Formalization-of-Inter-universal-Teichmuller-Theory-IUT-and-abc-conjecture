import Mathlib
example {G H : Type*} [CommMonoid G] [Group H] (e : G ≃* H) : Group G := by
  letI : Group G :=
  { (inferInstance : Monoid G) with
    inv := fun x => e.symm ((e x)⁻¹)
    inv_mul_cancel := by
      intro a
      apply e.injective
      simp [map_mul] }
  exact inferInstance
