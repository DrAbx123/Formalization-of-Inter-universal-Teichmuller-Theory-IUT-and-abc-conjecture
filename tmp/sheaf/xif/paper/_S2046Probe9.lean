import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace S2046Probe

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable def unitPartValue (x : ℚ_[p]ˣ) : ℚ_[p] :=
  x.val * (p : ℚ_[p]) ^ (-(x.val.valuation) : ℤ)

lemma norm_unitPartValue (x : ℚ_[p]ˣ) : ‖unitPartValue p x‖ = 1 := by
  rw [unitPartValue, norm_mul, Padic.norm_eq_zpow_neg_valuation (Units.ne_zero x),
    Padic.norm_p_zpow]
  rw [← zpow_add₀]
  · simp
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

noncomputable def unitPart (x : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_unitPartValue p x)

lemma unitPart_coe (x : ℚ_[p]ˣ) :
    ((unitPart p x : ℤ_[p]) : ℚ_[p]) = unitPartValue p x := by
  exact PadicInt.mkUnits_eq (norm_unitPartValue p x)

lemma unitPart_mul_coe (x y : ℚ_[p]ˣ) :
    ((unitPart p (x * y) : ℤ_[p]) : ℚ_[p]) =
      ((unitPart p x : ℤ_[p]) : ℚ_[p]) * ((unitPart p y : ℤ_[p]) : ℚ_[p]) := by
  rw [unitPart_coe, unitPart_coe, unitPart_coe, unitPartValue, unitPartValue, unitPartValue,
    Units.val_mul, Padic.valuation_mul (Units.ne_zero x) (Units.ne_zero y), neg_add,
    zpow_add₀]
  · ring
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

noncomputable def unitPartHom : ℚ_[p]ˣ →* ℤ_[p]ˣ where
  toFun := unitPart p
  map_one' := by
    ext
    apply PadicInt.ext
    rw [unitPart_coe]
    simp [unitPartValue, Padic.valuation_one]
  map_mul' x y := by
    ext
    apply PadicInt.ext
    exact unitPart_mul_coe p x y

end S2046Probe
