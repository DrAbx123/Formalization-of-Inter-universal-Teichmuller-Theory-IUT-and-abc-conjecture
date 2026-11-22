import tmp.sheaf.xif.paper.Mzk1IVThm110PrincipalDimInstantiateActual
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitValuationActual
import tmp.sheaf.xif.paper.Mzk1IVThm110QpDecompActual
import tmp.sheaf.xif.paper.Mzk1IVThm110PrincipalDimActual
import Mathlib.NumberTheory.Padics.PadicNumbers
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimAssemblyActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimInstantiateActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitValuationActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110QpDecompActual
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
/-- Assembly with hnorm and hchar discharged; only the scalar/unit action bridge
hact remains explicit. -/
theorem principalDim_log_scaling_of_decomp
    (lam : ℚ_[p]) (k : ℤ) (u : ℤ_[p]ˣ)
    (hlam0 : lam ≠ 0)
    (hdecomp : lam = (p : ℚ_[p]) ^ k * (u : ℚ_[p]))
    (hact : (lam • arithmeticTupleCanonicalUnitReference places tuple) =
      ((principalDimUnit (p := p) places tuple k u :
          ArithmeticTensorTupleBlock places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple)) :
    Real.log (μ (lam • arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal +
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) *
          Real.log ‖lam‖ := by
  have hnorm : Real.log ‖lam‖ = -((k : ℝ) * Real.log (p : ℝ)) :=
    log_norm_decomp (p := p) hlam0 hdecomp (zpUnit_valuation_eq_zero u)
  have hchar := hchar_principalDimUnit (p := p) places tuple k u μ
  exact principalDim_log_scaling_actual (p := p) places tuple μ lam k u
    hdecomp hnorm hact hchar
/-- Exact missing source: the scalar Qp action equals the unit action on O. -/
def exactMissingHact : List String :=
  [ "lam • O = ((principalDimUnit k u : X) • O) for lam = p^k*u",
    "equivalently principalDimUnit k u acts by algebraMap lam on O",
    "requires scalar/unit action compatibility on the tensor block" ]
theorem exactMissingHact_length : exactMissingHact.length = 3 := rfl
#check principalDim_log_scaling_of_decomp
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalDimAssemblyActual
end