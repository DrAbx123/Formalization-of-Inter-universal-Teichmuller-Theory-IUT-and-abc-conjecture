import tmp.sheaf.xif.paper.EtTh09ThetaShiftCorollariesActual
import tmp.sheaf.xif.paper.EtTh08ThetaTransformationActual

/-!
# Mzk1EtThShiftFractionLawActual — general fractional form of the abstract theta shift law
(new theorem from the existing EtTh08/EtTh09 assets: shift data => quotient formula for all
integer exponents). No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
open LeanFormal.IUT.XiFPaper.EtTh08ThetaTransformationActual
open LeanFormal.IUT.XiFPaper.EtTh09ThetaShiftCorollariesActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThShiftFractionLawActual

universe u

/-- Derived: for any shift data, the normalized quotient f(r^a U0)/f(U0) is the explicit
characteristic factor (generalizes EtTh09 a = 1 to all integer exponents a). -/
theorem etTh08_shift_fraction {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) (hf : f U0 ≠ 0) (a : ℤ) :
    f (r ^ a * U0) / f U0 =
      (-1 : L) ^ a * r ^ (-(a ^ 2)) * U0 ^ (-(2 * a)) := by
  rw [h.shift a]
  exact mul_div_cancel_right₀ _ hf

/-- Derived: the a = 0 case of the fractional form is the normalization. -/
theorem etTh08_shift_fraction_zero {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) (hf : f U0 ≠ 0) :
    f U0 / f U0 = 1 :=
  div_self hf

/-- Derived: the a = 1 case of the fractional form agrees with EtTh09's quotient law. -/
theorem etTh08_shift_fraction_one {L : Type u} [Field L] {f : L → L} {r U0 : L}
    (h : ThetaShiftData f r U0) (hf : f U0 ≠ 0) :
    f (r * U0) / f U0 = (-1 : L) * r ^ (-1 : ℤ) * U0 ^ (-2 : ℤ) := by
  rw [etTh08_shift_fraction h hf 1]
  norm_num

#check etTh08_shift_fraction
#check etTh08_shift_fraction_zero
#check etTh08_shift_fraction_one

end LeanFormal.IUT.XiFPaper.Mzk1EtThShiftFractionLawActual
end
