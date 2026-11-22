import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace Probe2565f

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

example : ∀ a : ZMod 613, ((C 2 * X + C 3 : (ZMod 613)[X])).eval a = 2 * a + 3 := by
  decide

#check @Polynomial.eq_of_natDegree_lt_card_of_eval_eq'

example : (C 2 * (C 5 + X) + C 3 : (ZMod 613)[X]) = C 13 + C 2 * X := by
  ext n
  interval_cases n <;> simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X] <;> decide

end Probe2565f
