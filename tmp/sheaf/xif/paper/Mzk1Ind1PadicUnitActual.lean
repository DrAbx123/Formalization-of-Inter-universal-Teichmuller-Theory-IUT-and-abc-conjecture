import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1PadicUnitActual

variable {p r : Nat} [Fact p.Prime]

theorem padicInt_isUnit_natCast_of_coprime (h : p.Coprime r) :
    IsUnit ((r : ℕ) : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact h

theorem padicInt_isUnit_natCast_pow_of_coprime (h : p.Coprime r) (n : Nat) :
    IsUnit (((r ^ n : ℕ) : ℤ_[p])) := by
  rw [Nat.cast_pow]
  exact (padicInt_isUnit_natCast_of_coprime h).pow n

#print axioms padicInt_isUnit_natCast_of_coprime
#print axioms padicInt_isUnit_natCast_pow_of_coprime
end LeanFormal.IUT.XiFPaper.Mzk1Ind1PadicUnitActual