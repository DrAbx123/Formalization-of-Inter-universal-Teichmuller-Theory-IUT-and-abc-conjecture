import tmp.sheaf.xif.paper.S2806TateParameterActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2806TateParameterActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

local instance s2836GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2836UniformizerNoRootSystemActual

variable (w : NumberField.FinitePlace GaussianField)

/-- The exact uniformizer unit from S2806. -/
noncomputable def S2836QUnit : (Completion w)ˣ :=
  Units.mk0 (S2806Candidate w).q (S2806Candidate w).q_ne_zero

/-- The unit has valuation exactly exp (-1). -/
theorem S2836QUnit_valuation :
    Valued.v ((S2836QUnit w : (Completion w)ˣ) : Completion w) =
      WithZero.exp (-1 : Int) := by
  change Valued.v ((S2806Candidate w).q) = WithZero.exp (-1 : Int)
  rw [S2806Candidate, S2806Q_valuation_bridge, S2806Q_spec]

/-- The value group has no square root of exp (-1). -/
theorem S2836_no_square_root_exp_neg_one
    (x : WithZero (Multiplicative Int)) (hx : x ^ 2 = WithZero.exp (-1 : Int)) : False := by
  by_cases h0 : x = 0
  · rw [h0] at hx
    exact (WithZero.exp_ne_zero (a := (-1 : Int))) hx.symm
  · have hlog : x = WithZero.exp (WithZero.log x) := (WithZero.exp_log h0).symm
    rw [hlog] at hx
    have hx' : WithZero.exp (WithZero.log x + WithZero.log x) =
        WithZero.exp (-1 : Int) := by
      simpa [pow_two, WithZero.exp_add] using hx
    have hEq : WithZero.log x + WithZero.log x = -1 :=
      WithZero.exp_injective hx'
    omega

/-- No NatRootSystem for the exact S2806 uniformizer unit. -/
theorem S2836_no_NatRootSystem :
    ¬ Nonempty (NatRootSystem (S2836QUnit w)) := by
  rintro ⟨R⟩
  let u : (Completion w)ˣ := R.root 2
  have hu : u ^ 2 = S2836QUnit w := by
    simpa [u] using R.pow_self 2 (by norm_num)
  have huv : ((u : (Completion w)ˣ) : Completion w) ^ 2 =
      ((S2836QUnit w : (Completion w)ˣ) : Completion w) := by
    rw [← Units.val_pow_eq_pow_val, hu]
  have hval : (Valued.v (((u : (Completion w)ˣ) : Completion w))) ^ 2 =
      WithZero.exp (-1 : Int) := by
    rw [← map_pow, huv, S2836QUnit_valuation]
  exact S2836_no_square_root_exp_neg_one _ hval

#check S2836QUnit
#check S2836QUnit_valuation
#check S2836_no_square_root_exp_neg_one
#check S2836_no_NatRootSystem
#print axioms S2836_no_NatRootSystem

end LeanFormal.IUT.XiFPaper.S2836UniformizerNoRootSystemActual
end
