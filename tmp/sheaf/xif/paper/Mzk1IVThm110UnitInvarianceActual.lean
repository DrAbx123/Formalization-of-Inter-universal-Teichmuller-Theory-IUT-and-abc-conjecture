import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
open scoped Pointwise
/-! Unit invariance of the canonical integral lattice O = integralClosure Zp.

For u : units of Zp, algebraMap u and its inverse are integral over Zp, so
multiplication by algebraMap u preserves O setwise. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
local notation "X" => ArithmeticTensorTupleBlock places tuple
/-- The embedded unit is integral over Zp, hence lies in O. -/
theorem algebraMap_unit_mem_integralClosure (u : ℤ_[p]ˣ) :
    algebraMap ℤ_[p] X (u : ℤ_[p]) ∈
      (integralClosure ℤ_[p] X : Set X) := by
  exact algebraMap_mem (integralClosure ℤ_[p] X) (u : ℤ_[p])
/-- Multiplication by the embedded unit preserves the integral lattice. -/
theorem algebraMap_unit_mul_mem_integralClosure (u : ℤ_[p]ˣ)
    {y : X} (hy : y ∈ (integralClosure ℤ_[p] X : Set X)) :
    algebraMap ℚ_[p] X (u : ℚ_[p]) * y ∈
      (integralClosure ℤ_[p] X : Set X) := by
  have hcomm : algebraMap ℚ_[p] X (u : ℚ_[p]) =
      algebraMap ℤ_[p] X (u : ℤ_[p]) := by
    rw [show (u : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) by simp]
    exact (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] X (u : ℤ_[p])).symm
  rw [hcomm]
  exact mul_mem (algebraMap_unit_mem_integralClosure (p := p) places tuple u) hy
/-- Multiplication by the inverse embedded unit preserves the integral lattice. -/
theorem algebraMap_unit_inv_mul_mem_integralClosure (u : ℤ_[p]ˣ)
    {y : X} (hy : y ∈ (integralClosure ℤ_[p] X : Set X)) :
    algebraMap ℚ_[p] X ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) * y ∈
      (integralClosure ℤ_[p] X : Set X) := by
  have hcast : ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) =
      algebraMap ℤ_[p] ℚ_[p] ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := rfl
  have hcomm : algebraMap ℚ_[p] X ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) =
      algebraMap ℤ_[p] X ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [hcast]
    exact (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] X
      ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).symm
  rw [hcomm]
  exact mul_mem (algebraMap_unit_mem_integralClosure (p := p) places tuple (u⁻¹)) hy
/-- The map x ↦ algebraMap(u) * x maps O onto O. -/
theorem algebraMap_unit_image_canonicalUnitReference_eq (u : ℤ_[p]ˣ) :
    ((fun x : X => algebraMap ℚ_[p] X (u : ℚ_[p]) * x) ''
        arithmeticTupleCanonicalUnitReference places tuple) =
      arithmeticTupleCanonicalUnitReference places tuple := by
  rw [arithmeticTupleCanonicalUnitReference_eq_integralClosure]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact algebraMap_unit_mul_mem_integralClosure (p := p) places tuple u hy
  · intro hx
    refine ⟨algebraMap ℚ_[p] X ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) * x, ?_, ?_⟩
    · exact algebraMap_unit_inv_mul_mem_integralClosure (p := p) places tuple u hx
    · have hscalar : (u : ℚ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) = 1 := by
        change algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) *
          algebraMap ℤ_[p] ℚ_[p] ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1
        rw [← map_mul, Units.mul_inv, map_one]
      have hprod : algebraMap ℚ_[p] X (u : ℚ_[p]) *
          algebraMap ℚ_[p] X ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) = 1 := by
        rw [← map_mul, hscalar, map_one]
      beta_reduce
      rw [← mul_assoc, hprod, one_mul]
/-- The embedded unit as a unit of the tensor block. -/
noncomputable def algebraMapUnit (u : ℤ_[p]ˣ) : Xˣ where
  val := algebraMap ℚ_[p] X (u : ℚ_[p])
  inv := algebraMap ℚ_[p] X ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p])
  val_inv := by
    have hscalar : (u : ℚ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) = 1 := by
      change algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) *
        algebraMap ℤ_[p] ℚ_[p] ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1
      rw [← map_mul, Units.mul_inv, map_one]
    rw [← map_mul, hscalar, map_one]
  inv_val := by
    have hscalar : ((u⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) * (u : ℚ_[p]) = 1 := by
      change algebraMap ℤ_[p] ℚ_[p] ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
        algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) = 1
      rw [← map_mul, Units.inv_mul, map_one]
    rw [← map_mul, hscalar, map_one]
/-- The unit action on the canonical integral lattice is trivial. -/
theorem algebraMapUnit_smul_canonicalUnitReference_eq (u : ℤ_[p]ˣ) :
    ((algebraMapUnit (p := p) places tuple u : X) •
        arithmeticTupleCanonicalUnitReference places tuple) =
      arithmeticTupleCanonicalUnitReference places tuple := by
  change ((fun x : X => algebraMap ℚ_[p] X (u : ℚ_[p]) * x) ''
      arithmeticTupleCanonicalUnitReference places tuple) =
    arithmeticTupleCanonicalUnitReference places tuple
  exact algebraMap_unit_image_canonicalUnitReference_eq (p := p) places tuple u
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitInvarianceActual
end
