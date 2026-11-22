import tmp.sheaf.xif.paper.Mzk1IVThm110PrincipalDimAssemblyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSharpUpperBound
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitRegionScalingActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimAssemblyActual
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
/-- PrincipalDim scaling for the actual IQ unit region: only hact remains explicit. -/
theorem unitRegionLog_eq_canonical_add_principalDim
    (k : ℤ) (u : ℤ_[p]ˣ)
    (hdecomp : arithmeticTupleIQHullUnitScale places tuple =
      (p : ℚ_[p]) ^ k * (u : ℚ_[p]))
    (hact : (arithmeticTupleIQHullUnitScale places tuple •
        arithmeticTupleCanonicalUnitReference places tuple) =
      ((principalDimUnit (p := p) places tuple k u :
          ArithmeticTensorTupleBlock places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple)) :
    arithmeticTupleIQHullUnitRegionHaarLog places tuple μ =
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal +
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) *
          Real.log ‖arithmeticTupleIQHullUnitScale places tuple‖ := by
  have h := principalDim_log_scaling_of_decomp (p := p) places tuple μ
    (arithmeticTupleIQHullUnitScale places tuple) k u
    (arithmeticTupleIQHullUnitScale_ne_zero places tuple) hdecomp hact
  simpa [arithmeticTupleIQHullUnitRegionHaarLog, arithmeticTupleIQHullUnitRegion] using h
/-- Exact remaining floor inputs. -/
def floorRemainingInputs : List String :=
  [ "unitRegionLog = -nativeGlobalQPilotNormalizedLogMagnitude T",
    "1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T" ]
theorem floorRemainingInputs_length : floorRemainingInputs.length = 2 := rfl
#check unitRegionLog_eq_canonical_add_principalDim
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitRegionScalingActual
end