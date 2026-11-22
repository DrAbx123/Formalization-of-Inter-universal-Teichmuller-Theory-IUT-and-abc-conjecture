import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

noncomputable section
open MvPolynomial

namespace DegreeTest

variable {K : Type} [Field K]

example (a b c : K) :
    MvPolynomial.degreeOf 1
      ((MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 2 -
        ((MvPolynomial.X 0) ^ 3 +
          MvPolynomial.C a * (MvPolynomial.X 0) ^ 2 +
          MvPolynomial.C b * (MvPolynomial.X 0) + MvPolynomial.C c)) = 2 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [sub_eq_add_neg, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt]
  · simp
  · have hX : MvPolynomial.degreeOf 1
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_X_of_ne h10
    have hX2 : MvPolynomial.degreeOf 1
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2) = 0 :=
      MvPolynomial.degreeOf_X_pow_of_ne 2 h10
    have hX3 : MvPolynomial.degreeOf 1
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 3) = 0 :=
      MvPolynomial.degreeOf_X_pow_of_ne 3 h10
    have hCa : MvPolynomial.degreeOf 1
        (MvPolynomial.C a : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_C a 1
    have hCb : MvPolynomial.degreeOf 1
        (MvPolynomial.C b : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_C b 1
    have hCc : MvPolynomial.degreeOf 1
        (MvPolynomial.C c : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_C c 1
    have hmul : ∀ (p q : MvPolynomial (Fin 2) K),
        MvPolynomial.degreeOf 1 (p * q) ≤
          MvPolynomial.degreeOf 1 p + MvPolynomial.degreeOf 1 q :=
      fun p q => MvPolynomial.degreeOf_mul_le 1 p q
    have hterm2 : MvPolynomial.degreeOf 1
        (MvPolynomial.C a * (MvPolynomial.X 0) ^ 2 : MvPolynomial (Fin 2) K) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      calc MvPolynomial.degreeOf 1
            (MvPolynomial.C a * (MvPolynomial.X 0) ^ 2 : MvPolynomial (Fin 2) K)
          ≤ MvPolynomial.degreeOf 1 (MvPolynomial.C a) +
              MvPolynomial.degreeOf 1 ((MvPolynomial.X 0) ^ 2) := hmul _ _
        _ = 0 := by rw [hCa, hX2, add_zero]
    have hterm1 : MvPolynomial.degreeOf 1
        (MvPolynomial.C b * MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      calc MvPolynomial.degreeOf 1
            (MvPolynomial.C b * MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          ≤ MvPolynomial.degreeOf 1 (MvPolynomial.C b) +
              MvPolynomial.degreeOf 1 (MvPolynomial.X 0) := hmul _ _
        _ = 0 := by rw [hCb, hX, add_zero]
    have hrest : MvPolynomial.degreeOf 1
        (-(((MvPolynomial.X 0) ^ 3 +
          MvPolynomial.C a * (MvPolynomial.X 0) ^ 2 +
          MvPolynomial.C b * (MvPolynomial.X 0) + MvPolynomial.C c)) :
            MvPolynomial (Fin 2) K) ≤ 1 := by
      rw [MvPolynomial.degreeOf_neg]
      calc MvPolynomial.degreeOf 1
            ((MvPolynomial.X 0) ^ 3 +
              MvPolynomial.C a * (MvPolynomial.X 0) ^ 2 +
              MvPolynomial.C b * (MvPolynomial.X 0) + MvPolynomial.C c :
                MvPolynomial (Fin 2) K)
          ≤ max (MvPolynomial.degreeOf 1 ((MvPolynomial.X 0) ^ 3 +
                MvPolynomial.C a * (MvPolynomial.X 0) ^ 2))
              (MvPolynomial.degreeOf 1 (MvPolynomial.C b * MvPolynomial.X 0 +
                MvPolynomial.C c)) := MvPolynomial.degreeOf_add_le _ _ _
        _ ≤ 1 := by
          rw [hX3]
          -- remaining goals
          sorry
      done

end DegreeTest
