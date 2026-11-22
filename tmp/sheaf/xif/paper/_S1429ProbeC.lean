import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

#check WithZero.coe_unzero
#check WithZero.exp
#check WithZero.log
#check WithZero.exp_log
#check WithZero.log_exp
#check nsmul_eq_mul
#check WithZero.exp_injective
#check Multiplicative.toAdd

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p) (q : FinitePlaceQCandidate place.val)
variable (x : WithZero (Multiplicative Int)) (hx : x ≠ 0)

example : WithZero.exp (Multiplicative.toAdd (WithZero.unzero hx)) = x := by
  simp

example : WithZero.exp (WithZero.log x) = x := by
  exact WithZero.exp_log hx

example : WithZero.log (WithZero.exp (3 : Int)) = (Multiplicative.ofAdd (3 : Int)) := by
  simp

example : (WithZero.log x).toAdd = (WithZero.log x).toAdd := rfl

example : ((WithZero.log x).toAdd) = Multiplicative.toAdd (WithZero.log x) := rfl
