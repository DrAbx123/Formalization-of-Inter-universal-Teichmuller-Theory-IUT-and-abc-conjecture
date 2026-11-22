import tmp.sheaf.xif.paper.Mzk1IVThm110PrincipalDimActual
import tmp.sheaf.xif.paper.Mzk1IVThm110QpDecompActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.NumberTheory.Padics.PadicNumbers
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimInstantiateActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimActual
open scoped Pointwise
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable [ContinuousConstSMul (ArithmeticTensorTupleBlock places tuple)ˣ
  (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
/-- Log-norm formula from lam = p^k*u and valuation 0 of the unit. -/
theorem log_norm_decomp {lam : ℚ_[p]} {k : ℤ} {u : ℤ_[p]ˣ}
    (hlam0 : lam ≠ 0)
    (hdecomp : lam = (p : ℚ_[p]) ^ k * (u : ℚ_[p]))
    (hvalu : (u : ℚ_[p]).valuation = 0) :
    Real.log ‖lam‖ = -((k : ℝ) * Real.log (p : ℝ)) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hu0 : (u : ℚ_[p]) ≠ 0 := by
    intro h
    have hZ : (u : ℤ_[p]) = 0 := Subtype.ext (by simpa using h)
    exact u.ne_zero hZ
  have hval : lam.valuation = k := by
    rw [hdecomp, Padic.valuation_mul (zpow_ne_zero k hp0) hu0,
      Padic.valuation_zpow, Padic.valuation_p, hvalu]
    ring
  rw [Padic.norm_eq_zpow_neg_valuation hlam0, hval]
  rw [Real.log_zpow]
  push_cast
  ring
/-- Character of principalDimUnit k u as a real number. -/
theorem hchar_principalDimUnit (k : ℤ) (u : ℤ_[p]ˣ)
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure] :
    (distribHaarChar (ArithmeticTensorTupleBlock places tuple)
      (principalDimUnit (p := p) places tuple k u) : ℝ) =
      (p : ℝ) ^ (-(k : ℝ) * (Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple) : ℝ)) := by
  have hsplit : principalDimUnit (p := p) places tuple k u =
      arithmeticTuplePrimeScalarUnit places tuple ^ k *
        algebraMapUnit (p := p) places tuple u := rfl
  rw [hsplit, map_mul]
  have hunit : distribHaarChar (ArithmeticTensorTupleBlock places tuple)
      (algebraMapUnit (p := p) places tuple u) = 1 :=
    distribHaarChar_algebraMapUnit_eq_one (p := p) places tuple u μ
  rw [hunit, mul_one]
  have hlog := real_log_distribHaarChar_arithmeticTuplePrimeScalarUnit_zpow
    (p := p) places tuple (k := k)
  have hpos : (0 : ℝ) < (distribHaarChar (ArithmeticTensorTupleBlock places tuple)
      (arithmeticTuplePrimeScalarUnit places tuple ^ k) : ℝ) :=
    NNReal.coe_pos.mpr (distribHaarChar_pos (A := ArithmeticTensorTupleBlock places tuple))
  rw [← Real.exp_log hpos, hlog]
  rw [Real.rpow_def_of_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos)]
  congr 1
  ring
#check log_norm_decomp
#check hchar_principalDimUnit
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimInstantiateActual
end