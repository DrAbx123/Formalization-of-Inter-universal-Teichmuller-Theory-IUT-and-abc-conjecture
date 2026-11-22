import tmp.sheaf.xif.paper.Mzk1IVThm110HaarUnitInvarianceActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
open scoped Pointwise
/-! Principal-dimension Haar scaling from the Qp decomposition lambda = p^k * u.

Green inputs:
* distribHaarChar arithmeticTuplePrimeScalarUnit = p^{-D};
* distribHaarChar (algebraMapUnit u) = 1;
* measure scaling under a unit from distribHaarChar_mul.

The two explicit bridges are:
* lambda = p^k * u and the scalar/unit action equality;
* the p-adic norm/log value of lambda.
No fake: these are hypotheses, not derived. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimScalingActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
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
/-- PrincipalDim scaling, conditional on the Qp decomposition, an abstract unit
action bridge, and the p-adic norm/log value. -/
theorem principalDim_log_scaling
    (lam : ℚ_[p]) (k : ℤ) (u : ℤ_[p]ˣ)
    (g : (ArithmeticTensorTupleBlock places tuple)ˣ)
    (hlam : lam = (p : ℚ_[p]) ^ k * (u : ℚ_[p]))
    (hact : (lam • arithmeticTupleCanonicalUnitReference places tuple) =
      ((g : ArithmeticTensorTupleBlock places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple))
    (hchar : (distribHaarChar (ArithmeticTensorTupleBlock places tuple) g : ℝ) =
      (p : ℝ) ^ (-(k : ℝ) * (Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple) : ℝ)))
    (hnorm : Real.log ‖lam‖ = -((k : ℝ) * Real.log (p : ℝ))) :
    Real.log (μ (lam • arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal +
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) *
          Real.log ‖lam‖ := by
  let O := arithmeticTupleCanonicalUnitReference places tuple
  have hμ : μ (g • O) =
      (distribHaarChar (ArithmeticTensorTupleBlock places tuple) g : ENNReal) * μ O :=
    (distribHaarChar_mul (μ := μ) (g := g) O).symm
  have hpos : 0 < μ O :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).2.1
  have hfin : μ O < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).2.2
  change Real.log (μ (lam • O)).toReal =
    Real.log (μ O).toReal +
      (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) * Real.log ‖lam‖
  rw [hact]
  change Real.log (μ (g • O)).toReal =
    Real.log (μ O).toReal +
      (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) * Real.log ‖lam‖
  rw [hμ, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [Real.log_mul]
  · rw [hchar, hnorm]
    rw [Real.log_rpow (by exact_mod_cast (Fact.out : Nat.Prime p).pos)]
    ring
  · exact NNReal.coe_ne_zero.mpr
      (distribHaarChar_pos (A := ArithmeticTensorTupleBlock places tuple) (g := g)).ne'
  · exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
#check principalDim_log_scaling
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimScalingActual
end
