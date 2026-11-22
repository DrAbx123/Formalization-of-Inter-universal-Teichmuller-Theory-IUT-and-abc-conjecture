import tmp.sheaf.xif.paper.S2574TateMinimalFinalActual
import Mathlib.Algebra.Polynomial.Splits

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2575TateMultiplicativeActual

theorem S2575_X_sq_add_X_splits (S : Type*) [CommRing S] :
    Polynomial.Splits ((Polynomial.X : S[X]) ^ 2 + Polynomial.X) := by
  have h : (Polynomial.X : S[X]) ^ 2 + Polynomial.X =
      Polynomial.X * (Polynomial.X + Polynomial.C 1) := by
    simp only [pow_two, mul_add, mul_one, map_one]
  rw [h]
  exact (Polynomial.Splits.X).mul (Polynomial.Splits.X_add_C 1)

theorem S2575_X_sq_add_X_eq_mul (S : Type*) [CommRing S] :
    (Polynomial.X : S[X]) ^ 2 + Polynomial.X =
      Polynomial.X * (Polynomial.X + 1) := by
  simp only [pow_two, mul_add, mul_one, map_one]

#check S2575_X_sq_add_X_splits
#check S2575_X_sq_add_X_eq_mul
#print axioms S2575_X_sq_add_X_splits
end LeanFormal.IUT.XiFPaper.S2575TateMultiplicativeActual
end