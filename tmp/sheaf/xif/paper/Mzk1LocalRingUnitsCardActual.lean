/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib
/-! # Units of a finite local ring: complement of the maximal ideal -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
/-- In a finite local ring, the number of units is the total cardinal minus the maximal ideal. -/
theorem natCard_units_eq_card_sub_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R]
    [Finite R] :
    Nat.card Rˣ = Nat.card R - Nat.card (IsLocalRing.maximalIdeal R) := by
  classical
  letI := Fintype.ofFinite R
  have hcomp := Fintype.card_subtype_compl (fun x : R => IsUnit x)
  have hunits : Nat.card Rˣ = Fintype.card {x : R // IsUnit x} := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_congr ?_
    exact { toFun := fun u => ⟨(u : R), u.isUnit⟩
            invFun := fun x => x.2.unit
            left_inv := fun u => Units.ext rfl
            right_inv := fun x => Subtype.ext (IsUnit.unit_spec x.2) }
  have hnonunits : Nat.card (IsLocalRing.maximalIdeal R) = Fintype.card {x : R // ¬ IsUnit x} := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_congr ?_
    exact { toFun := fun x => ⟨(x : R), (IsLocalRing.mem_maximalIdeal (x : R)).mpr x.2⟩
            invFun := fun x => ⟨(x : R), (IsLocalRing.mem_maximalIdeal (x : R)).mp x.2⟩
            left_inv := fun x => rfl
            right_inv := fun x => rfl }
  rw [hunits, hnonunits, Nat.card_eq_fintype_card, hcomp]
  exact (Nat.sub_sub_self (Fintype.card_subtype_le (fun x : R => IsUnit x))).symm
end LeanFormal.IUT.LocalFieldLogarithm
end