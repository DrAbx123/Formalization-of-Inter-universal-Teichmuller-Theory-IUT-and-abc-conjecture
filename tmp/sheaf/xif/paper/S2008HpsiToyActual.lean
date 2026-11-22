import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Field.Rat
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2008HpsiToyActual

theorem S2008C_mul_C (a b : ℚ) :
    (C a * C b : ℚ[X]) = C (a * b) := by
  rw [← Polynomial.C_mul]

theorem S2008C_mul_C_mul_X_pow (a b : ℚ) (n : ℕ) :
    (C a * C b * X ^ n : ℚ[X]) = C (a * b) * X ^ n := by
  rw [S2008C_mul_C]

theorem S2008C_pow_eq (a : ℚ) (n : ℕ) :
    ((C a : ℚ[X]) ^ n) = C (a ^ n) := by
  rw [Polynomial.C_pow]

theorem S2008mul_C_mul_C (p : ℚ[X]) (a b : ℚ) :
    p * C a * C b = p * C (a * b) := by
  rw [mul_assoc, S2008C_mul_C]

theorem S2008mul_C_mul_nat (p : ℚ[X]) (a : ℚ) (n : ℕ) :
    p * C a * (n : ℚ[X]) = p * C (a * n) := by
  rw [mul_assoc, ← Polynomial.C_eq_natCast n, ← Polynomial.C_mul]

theorem S2008mul_C_mul_int (p : ℚ[X]) (a : ℚ) (n : ℤ) :
    p * C a * (n : ℚ[X]) = p * C (a * n) := by
  rw [mul_assoc, ← Polynomial.C_eq_intCast n, ← Polynomial.C_mul]

lemma S2008mul_C_mul_ofNat (p : ℚ[X]) (a : ℚ) (n : ℕ) [n.AtLeastTwo] :
    p * C a * (OfNat.ofNat n : ℚ[X]) = p * C (a * n) := by
  rw [show (OfNat.ofNat n : ℚ[X]) = (n : ℚ[X]) from rfl]
  exact S2008mul_C_mul_nat p a n

lemma S2008mul_C_mul_ofNat' (p : ℚ[X]) (a : ℚ) (n : ℕ) [n.AtLeastTwo] :
    p * (C a * (OfNat.ofNat n : ℚ[X])) = p * C (a * n) := by
  rw [← mul_assoc, S2008mul_C_mul_ofNat]

lemma S2008mul_C_mul_nat' (p : ℚ[X]) (a : ℚ) (n : ℕ) :
    p * (C a * (n : ℚ[X])) = p * C (a * n) := by
  rw [← mul_assoc, S2008mul_C_mul_nat]

lemma S2008mul_C_mul_int' (p : ℚ[X]) (a : ℚ) (n : ℤ) :
    p * (C a * (n : ℚ[X])) = p * C (a * n) := by
  rw [← mul_assoc, S2008mul_C_mul_int]

theorem S2008natCast_eq_C (n : ℕ) :
    (n : ℚ[X]) = C (n : ℚ) := (Polynomial.C_eq_natCast n).symm

theorem S2008intCast_eq_C (n : ℤ) :
    (n : ℚ[X]) = C (n : ℚ) := (Polynomial.C_eq_intCast n).symm

theorem S2008C_eq_algebraMap (q : ℚ) :
    (C q : ℚ[X]) = algebraMap ℚ ℚ[X] q := rfl

#check S2008C_mul_C
#check S2008C_mul_C_mul_X_pow
#print axioms S2008C_mul_C_mul_X_pow
#print axioms S2008mul_C_mul_ofNat'
#print axioms S2008mul_C_mul_nat'
#print axioms S2008mul_C_mul_int'
#print axioms S2008mul_C_mul_ofNat
#print axioms S2008mul_C_mul_nat
#print axioms S2008mul_C_mul_int
#print axioms S2008natCast_eq_C
#print axioms S2008intCast_eq_C
#print axioms S2008C_pow_eq
#print axioms S2008mul_C_mul_C
end LeanFormal.IUT.XiFPaper.S2008HpsiToyActual
