/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

/-! # S45-free scaling route (normalized representative)

Given a default norm `r i = p ^ (-(c i))` and a normalized representative with
`‖q i‖ = r i ^ (1 / d i)` (e.g. from the general normalized norm formula on the
normalized carrier, where the default element has norm `r i^(1/d)`), the element
`g i := q i ^ d i` has default norm `‖g i‖ = r i = p ^ (-(c i))`.  Hence
`arithmeticTuplePureFractionalScalingData_ofGenerator` produces the pure fractional
scaling data with paper coefficients `c`, WITHOUT the S45 norm-ratio condition.

Caveat (explicit): `g` is the normalized representative of the default coefficient,
not the actual `q`; identifying actual `q` norms is exactly the S45/norm-instance
condition and is NOT claimed here.  No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S45FreeScalingRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- **Core norm lemma.**  If `‖x‖ = r^(1/d)` and `0 < r`, `d ≠ 0`, then
`‖x^d‖ = r`. -/
theorem norm_pow_eq_of_norm_eq_rpow {E : Type*} [NormedField E]
    (x : E) (r : ℝ) (d : ℕ) (hd : d ≠ 0) (hr : 0 < r)
    (h : ‖x‖ = r ^ ((1 : ℝ) / (d : ℝ))) : ‖x ^ d‖ = r := by
  rw [norm_pow, h]
  rw [← Real.rpow_natCast (r ^ ((1 : ℝ) / (d : ℝ))) d]
  rw [← Real.rpow_mul (le_of_lt hr)]
  rw [show ((1 : ℝ) / (d : ℝ)) * (d : ℝ) = 1 by field_simp]
  exact Real.rpow_one r

/-- The normalized representative of the default coefficient: `g i := q i ^ d i`. -/
noncomputable def normalizedScalingGenerator
    (q : (i : ι) → CommonPrimeCompletion (places i (tuple i))) (d : ι → ℕ) :
    (i : ι) → CommonPrimeCompletion (places i (tuple i)) :=
  fun i => q i ^ d i

/-- The normalized scaling generator has the default norm `r i = p^(-(c i))`. -/
theorem norm_normalizedScalingGenerator
    (c : ι → ℝ) (r : ι → ℝ) (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0) (hr : ∀ i, 0 < r i)
    (hpc : ∀ i, r i = (p : ℝ) ^ (-(c i)))
    (q : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hq : ∀ i, ‖q i‖ = (r i) ^ ((1 : ℝ) / (d i : ℝ))) :
    ∀ i, ‖normalizedScalingGenerator places tuple q d i‖ = (p : ℝ) ^ (-(c i)) := by
  intro i
  unfold normalizedScalingGenerator
  rw [norm_pow_eq_of_norm_eq_rpow (q i) (r i) (d i) (hd i) (hr i) (hq i)]
  exact hpc i

/-- **S45-free scaling data.**  The paper-coefficient pure fractional scaling data exists
given a normalized representative with `‖q i‖ = r i^(1/d i)`.  This does NOT use the S45
norm-ratio condition; identifying actual `q` norms remains explicit. -/
noncomputable def arithmeticTuplePureFractionalScalingData_ofNormalizedRepresentative
    (c : ι → ℝ) (r : ι → ℝ) (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0) (hr : ∀ i, 0 < r i)
    (hpc : ∀ i, r i = (p : ℝ) ^ (-(c i)))
    (q : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hq : ∀ i, ‖q i‖ = (r i) ^ ((1 : ℝ) / (d i : ℝ))) :
    ArithmeticTuplePureFractionalScalingData places tuple c :=
  arithmeticTuplePureFractionalScalingData_ofGenerator places tuple c
    (normalizedScalingGenerator places tuple q d)
    (norm_normalizedScalingGenerator places tuple c r d hd hr hpc q hq)

/-- **S45-free normalized volume consumer.**  For a normalized representative with
`‖q i‖ = r i^(1/d i)`, the paper-coefficient fractional lattice has the exact
normalized log volume `-(∑ c_i) log p`, with no S45 norm-ratio condition. -/
theorem arithmeticTupleNormalizedLogVolume_ofNormalizedRepresentative
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (c : ι → ℝ) (r : ι → ℝ) (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0) (hr : ∀ i, 0 < r i)
    (hpc : ∀ i, r i = (p : ℝ) ^ (-(c i)))
    (q : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hq : ∀ i, ‖q i‖ = (r i) ^ ((1 : ℝ) / (d i : ℝ))) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      ((arithmeticTupleFractionalLattice places tuple c *
        arithmeticTupleHolomorphicLattice places tuple :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      -((∑ i, c i) * Real.log (p : ℝ)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
    places tuple μ c (normalizedScalingGenerator places tuple q d)
    (norm_normalizedScalingGenerator places tuple c r d hd hr hpc q hq)

def s45FreeScalingRows : List (String × String × String) :=
  [ ("norm_pow_eq_of_norm_eq_rpow", "‖x‖ = r^(1/d), r>0, d≠0 => ‖x^d‖ = r", "PROVED"),
    ("normalizedScalingGenerator", "g_i := q_i ^ d_i (normalized representative)", "DEFINED"),
    ("norm_normalizedScalingGenerator", "‖g_i‖ = p^(-c_i) (default norm)", "PROVED"),
    ("arithmeticTuplePureFractionalScalingData_ofNormalizedRepresentative", "paper-coefficient scaling data WITHOUT S45", "PROVED (conditional on normalized representative)"),
    ("S45 / norm-instance equality", "actual q norms identification", "EXPLICIT CONDITION (not claimed)") ]

theorem s45FreeScalingRows_length : s45FreeScalingRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S45FreeScalingRouteActual

end