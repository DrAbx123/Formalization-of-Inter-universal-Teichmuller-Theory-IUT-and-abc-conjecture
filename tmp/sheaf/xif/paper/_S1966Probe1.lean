import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT

namespace Probe1966

#check Submonoid.mem_powers_iff
#check Submonoid.powers_eq_closure
#check pow_right_injective₀
#check Real.log_pos
#check Real.log_ne_zero
#check NNReal.coe_add
#check NNReal.coe_injective
#check HodgeTheater
#check FiniteThetaPacket.ofQ
#check FiniteThetaPacket.scale_eq
#check realThetaValue
#check Multiplicative.toAdd
#check Multiplicative.ofAdd
#check Submonoid

variable {l : PrimeGeFive}

example : Nonempty (Fin (lStar l.value)) := by
  refine ⟨⟨0, ?_⟩⟩
  have h5 : 5 <= l.value := l.ge_five
  unfold lStar
  omega

example : Nonempty (Fin (lStar l.value)) := by
  refine ⟨⟨1, ?_⟩⟩
  have h5 : 5 <= l.value := l.ge_five
  unfold lStar
  omega

example (p : Nat) (hp : Nat.Prime p) : 0 < Real.log p := by
  exact Real.log_pos (by exact_mod_cast hp.one_lt)

example (a : Real) (ha0 : 0 < a) (ha1 : a != 1) : Function.Injective (fun n : Nat => a ^ n) :=
  pow_right_injective₀ ha0 ha1

example (q : Real) (hq0 : 0 < q) (hq1 : q != 1) {m n : Nat} (h : q ^ m = q ^ n) : m = n :=
  pow_right_injective₀ hq0 hq1 h

end Probe1966
