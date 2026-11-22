import tmp.sheaf.xif.paper.Mzk1IVThm110QpDecompActual
import tmp.sheaf.xif.paper.Mzk1IVThm110PrincipalDimScalingActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HaarUnitInvarianceActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
/-! Actual PrincipalDim instantiation with explicit k,u. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimActual
open MeasureTheory MeasureTheory.Measure
open scoped Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimScalingActual
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
/-- The unit pU^k * algebraMapUnit u. -/
noncomputable def principalDimUnit (k : ℤ) (u : ℤ_[p]ˣ) :
    (ArithmeticTensorTupleBlock places tuple)ˣ :=
  arithmeticTuplePrimeScalarUnit places tuple ^ k *
    algebraMapUnit (p := p) places tuple u
/-- Actual PrincipalDim scaling with explicit decomposition k,u and explicit
scalar/unit action and character hypotheses. -/
theorem principalDim_log_scaling_actual
    (lam : ℚ_[p]) (k : ℤ) (u : ℤ_[p]ˣ)
    (hdecomp : lam = (p : ℚ_[p]) ^ k * (u : ℚ_[p]))
    (hnorm : Real.log ‖lam‖ = -((k : ℝ) * Real.log (p : ℝ)))
    (hact : (lam • arithmeticTupleCanonicalUnitReference places tuple) =
      ((principalDimUnit (p := p) places tuple k u :
          ArithmeticTensorTupleBlock places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple))
    (hchar : (distribHaarChar (ArithmeticTensorTupleBlock places tuple)
      (arithmeticTuplePrimeScalarUnit places tuple ^ k *
        algebraMapUnit (p := p) places tuple u) : ℝ) =
        (p : ℝ) ^ (-(k : ℝ) * (Module.finrank ℚ_[p]
          (ArithmeticTensorTupleBlock places tuple) : ℝ))) :
    Real.log (μ (lam • arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal +
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) *
          Real.log ‖lam‖ := by
  exact principalDim_log_scaling (p := p) places tuple μ lam k u
    (principalDimUnit (p := p) places tuple k u)
    hdecomp hact hchar hnorm
#check principalDim_log_scaling_actual
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimActual
end