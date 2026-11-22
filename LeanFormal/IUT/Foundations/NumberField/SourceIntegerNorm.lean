import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Integer casts in the unit ball of a normalized number-field completion

For K = NormalizedCompletion v at a number-field finite place, every natural
number cast into K has norm at most one: the integer is a p-adic integer in the
residue-character scalar field Q_l, and the normalized norm extends the Q_l norm.
No residue-character 2/3 exception. Scratch only; no production edits. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- Natural numbers are integral in the p-adic scalar field Q_l. -/
theorem padicScalarField_natCast_norm_le_one (place : NumberField.FinitePlace K)
    (n : Nat) : ‖(n : PadicScalarField place)‖ ≤ 1 := by
  by_cases h : (completionRationalPrime place).val ∣ n
  · exact (Padic.norm_natCast_lt_one_iff (p := (completionRationalPrime place).val)).mpr h |>.le
  · exact (Padic.norm_natCast_eq_one_iff (p := (completionRationalPrime place).val)).mpr
      ((Fact.out : (completionRationalPrime place).val.Prime).coprime_iff_not_dvd.mpr h) |>.le

/-- Instance hypothesis hint: every natural number cast into the actual
normalized completion has norm at most one. -/
theorem normalizedCompletion_natCast_norm_le_one (place : NumberField.FinitePlace K)
    (n : Nat) : ‖(n : NormalizedCompletion place)‖ ≤ 1 := by
  have hcast : (n : NormalizedCompletion place) =
      algebraMap (PadicScalarField place) (NormalizedCompletion place)
        (n : PadicScalarField place) :=
    (map_natCast (algebraMap (PadicScalarField place) (NormalizedCompletion place)) n).symm
  have hnorm : ‖algebraMap (PadicScalarField place) (NormalizedCompletion place)
      (n : PadicScalarField place)‖ = ‖(n : PadicScalarField place)‖ :=
    norm_algebraMap' (NormalizedCompletion place) (n : PadicScalarField place)
  rw [hcast, hnorm]
  exact padicScalarField_natCast_norm_le_one place n

end LeanFormal.IUT.NumberFieldFinitePlace
