import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Hom.Defs
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128AverageAttempt

variable {G : Type} [Group G] [Fintype G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- The averaging operator using an inverse of |G|. -/
noncomputable def S3128Average (hcard : IsUnit (Fintype.card G : A)) (b : A) : A :=
  ((hcard.unit⁻¹ : Aˣ) : A) * ∑ h : G, h • b

theorem S3128Average_invariant (hcard : IsUnit (Fintype.card G : A)) (b : A) (k : G) :
    k • S3128Average (G := G) (A := A) hcard b =
      S3128Average (G := G) (A := A) hcard b := by
  have hnat_smul : forall n : Nat, k • (n : A) = (n : A) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, smul_add, ih, smul_one]
  have hcard_smul : k • ((Fintype.card G : A)) = (Fintype.card G : A) :=
    hnat_smul (Fintype.card G)
  have hu_smul : k • ((hcard.unit : A)) = (hcard.unit : A) := by
    rw [hcard.unit_spec]
    exact hcard_smul
  have hu_unit : IsUnit ((hcard.unit : A)) := ⟨hcard.unit, rfl⟩
  have hu_inv_smul : k • (((hcard.unit⁻¹ : Aˣ) : A)) =
      ((hcard.unit⁻¹ : Aˣ) : A) := by
    apply IsUnit.mul_right_cancel hu_unit
    calc
      (k • (((hcard.unit⁻¹ : Aˣ) : A))) * (hcard.unit : A)
          = k • ((((hcard.unit⁻¹ : Aˣ) : A)) * (hcard.unit : A)) := by
            rw [smul_mul', hu_smul]
      _ = k • (1 : A) := by rw [Units.inv_mul]
      _ = (1 : A) := smul_one k
      _ = (((hcard.unit⁻¹ : Aˣ) : A)) * (hcard.unit : A) := by rw [Units.inv_mul]
  have hsum : k • (∑ h : G, h • b) = ∑ h : G, h • b := by
    change (MulSemiringAction.toRingHom G A k) (∑ h : G, h • b) = ∑ h : G, h • b
    rw [map_sum]
    apply Finset.sum_bij (fun h _ => k * h)
    · intro h _; exact Finset.mem_univ _
    · intro h _ h' _ hh; exact mul_left_cancel hh
    · intro h' _; exact ⟨k⁻¹ * h', Finset.mem_univ _, by simp⟩
    · intro h _; simp [mul_smul]
  rw [S3128Average, smul_mul', hu_inv_smul, hsum]

#check S3128Average_invariant

end LeanFormal.IUT.XiFPaper.S3128AverageAttempt
