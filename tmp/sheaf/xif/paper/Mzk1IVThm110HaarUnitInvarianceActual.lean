import tmp.sheaf.xif.paper.Mzk1IVThm110UnitInvarianceActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
open scoped Pointwise
/-! Haar invariance under the embedded Zp-unit action.

O = canonical unit reference has positive finite Haar mass and is fixed by
algebraMapUnit u.  distribHaarChar_eq_of_measure_smul_eq_mul then gives
distribHaarChar = 1, and distribHaarChar_mul gives μ(u • S) = μ S. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
variable [ContinuousConstSMul (ArithmeticTensorTupleBlock places tuple)ˣ
  (ArithmeticTensorTupleBlock places tuple)]
/-- The embedded Zp-unit has distributive Haar character 1. -/
theorem distribHaarChar_algebraMapUnit_eq_one
    (u : ℤ_[p]ˣ)
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure] :
    distribHaarChar (ArithmeticTensorTupleBlock places tuple)
      (algebraMapUnit (p := p) places tuple u) = 1 := by
  have hpos : 0 < μ (arithmeticTupleCanonicalUnitReference places tuple) :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).2.1
  have hfin : μ (arithmeticTupleCanonicalUnitReference places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).2.2
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (s := arithmeticTupleCanonicalUnitReference places tuple)
    (g := algebraMapUnit (p := p) places tuple u) hpos.ne' hfin.ne ?_
  rw [Units.smul_def, algebraMapUnit_smul_canonicalUnitReference_eq]
  simp
/-- The embedded Zp-unit action preserves every set's Haar measure. -/
theorem measure_algebraMapUnit_smul_eq (u : ℤ_[p]ˣ) (S : Set (ArithmeticTensorTupleBlock places tuple)) :
    μ ((algebraMapUnit (p := p) places tuple u : ArithmeticTensorTupleBlock places tuple) • S) =
      μ S := by
  have h := distribHaarChar_mul (μ := μ)
    (g := algebraMapUnit (p := p) places tuple u) S
  rw [distribHaarChar_algebraMapUnit_eq_one (p := p) (places := places) (tuple := tuple) (u := u) (μ := μ)] at h
  simpa [one_mul, Units.smul_def] using h.symm
#check distribHaarChar_algebraMapUnit_eq_one
#check measure_algebraMapUnit_smul_eq
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110HaarUnitInvarianceActual
end
