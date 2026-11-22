import tmp.sheaf.xif.paper.S2500CategoricalOtriangleActual

/-! # S2506: actual additive rho_v on O^◃ by log of the norm

On the actual nonzero integral-closure monoid, `rho x = Real.log ||x||` is
additive: `rho 1 = 0`, `rho (x*y) = rho x + rho y`.  This is an actual realified
map on O^◃; its restriction to the missing O^▷ generator layer remains to be
identified. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual

namespace LeanFormal.IUT.XiFPaper.S2506RhoVActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The actual additive rho_v on O^◃: log of the algebraic norm. -/
noncomputable def S2506Rho (x : S2500ODiamond p) : Real :=
  Real.log ‖(x.1.1 : AlgebraicClosure ℚ_[p])‖

theorem S2506Rho_one : S2506Rho p 1 = 0 := by
  unfold S2506Rho
  simp

theorem S2506Rho_mul (x y : S2500ODiamond p) :
    S2506Rho p (x * y) = S2506Rho p x + S2506Rho p y := by
  unfold S2506Rho
  have hx0 : (x : LocalAlgebraicIntegerRing p) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero x
  have hy0 : (y : LocalAlgebraicIntegerRing p) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero y
  have hx : (x.1.1 : AlgebraicClosure ℚ_[p]) ≠ 0 := by
    intro h; exact hx0 (Subtype.ext h)
  have hy : (y.1.1 : AlgebraicClosure ℚ_[p]) ≠ 0 := by
    intro h; exact hy0 (Subtype.ext h)
  have hxnorm : ‖(x.1.1 : AlgebraicClosure ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hx
  have hynorm : ‖(y.1.1 : AlgebraicClosure ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hy
  have hmul : (((x * y).1.1) : AlgebraicClosure ℚ_[p]) =
      (x.1.1 : AlgebraicClosure ℚ_[p]) *
        (y.1.1 : AlgebraicClosure ℚ_[p]) := rfl
  rw [hmul, norm_mul, Real.log_mul hxnorm hynorm]

#check S2506Rho
#check S2506Rho_one
#check S2506Rho_mul

end LeanFormal.IUT.XiFPaper.S2506RhoVActual
end
