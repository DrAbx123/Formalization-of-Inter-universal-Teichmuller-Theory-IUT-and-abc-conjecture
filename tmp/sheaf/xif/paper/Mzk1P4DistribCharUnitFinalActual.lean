/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Tactic
/-! # Integral units have trivial distributive Haar character -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P4DistribCharUnitFinalActual
open MeasureTheory LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Pointwise ENNReal NNReal
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [MeasurableSpace K] [BorelSpace K]
def integralUnitToFieldUnit (u : (Integers K)ˣ) : Kˣ :=
  Units.map (Subring.subtype (Integers K)) u
@[simp] theorem integralUnitToFieldUnit_val (u : (Integers K)ˣ) :
    ((integralUnitToFieldUnit u : Kˣ) : K) = (u : K) := by
  rfl
theorem integralUnit_smul_integers (u : (Integers K)ˣ) :
    (integralUnitToFieldUnit u : Kˣ) • (Integers K : Set K) = (Integers K : Set K) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Integers K).mul_mem u.val.property hx
  · intro hy
    refine ⟨((u⁻¹).val : K) * y, (Integers K).mul_mem (u⁻¹).val.property hy, ?_⟩
    have hmul : (u : K) * (((u⁻¹ : (Integers K)ˣ) : K)) = 1 := by
      exact_mod_cast u.val_inv
    simp only [Units.smul_def, integralUnitToFieldUnit_val]
    change (u : K) * ((((u⁻¹ : (Integers K)ˣ) : K)) * y) = y
    rw [← mul_assoc, hmul, one_mul]
theorem distribHaarChar_integralUnit_eq_one
    (μ : Measure K) (hμ : Measure.IsAddHaarMeasure μ)
    (hreg : MeasureTheory.Measure.Regular μ) (u : (Integers K)ˣ) :
    distribHaarChar K (integralUnitToFieldUnit u) = 1 := by
  letI := hμ
  letI := hreg
  have hpos := (LeanFormal.IUT.LocalFieldLogarithm.measure_localIntegers_pos_lt_top μ).1
  have hfin := (LeanFormal.IUT.LocalFieldLogarithm.measure_localIntegers_pos_lt_top μ).2
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hpos.ne' hfin.ne ?_
  rw [integralUnit_smul_integers]
  simp
theorem measure_integralUnit_smul
    (μ : Measure K) (hμ : Measure.IsAddHaarMeasure μ)
    (hreg : MeasureTheory.Measure.Regular μ) (u : (Integers K)ˣ) (S : Set K) :
    μ ((integralUnitToFieldUnit u : Kˣ) • S) = μ S := by
  letI := hμ
  letI := hreg
  rw [← distribHaarChar_mul μ (integralUnitToFieldUnit u) S]
  rw [distribHaarChar_integralUnit_eq_one μ hμ hreg u]
  norm_num
end LeanFormal.IUT.XiFPaper.Mzk1P4DistribCharUnitFinalActual
end