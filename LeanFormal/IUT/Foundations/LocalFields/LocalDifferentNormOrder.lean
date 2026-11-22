import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption

/-!
# Different orders in the norm normalization used by Step(v)

The different estimate uses the integer DVR order divided by the ramification
exponent. Step(v) uses `-log ‖delta‖ / log p`. These theorems identify the two
for the existing different generator, then transfer the actual tower estimate.
-/

namespace LeanFormal.IUT.LocalDifferentNormOrder

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IntegralTraceDualTensorInclusion LeanFormal.IUT.LocalDifferentUpperBound

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

/-- The actual different generator has exactly the paper-normalized norm. -/
theorem norm_differentGenerator_eq_prime_rpow_neg_paperOrder :
    ‖(localDifferentGenerator (p := p) (L := K) : K)‖ =
      (p : ℝ) ^ (-localDifferentPaperOrder (p := p) (L := K)) := by
  letI : IsDiscreteValuationRing (Integers K) := integersIsDiscreteValuationRing (p := p)
  obtain ⟨uniformizer, irreducible⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨order, unit, generator_eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (localDifferentGenerator_ne_zero (p := p) (L := K)) irreducible
  have unit_norm : ‖((unit : Integers K) : K)‖ = 1 := by
    have inverse_bound := (↑(unit⁻¹) : Integers K).property
    have unit_bound := (unit : Integers K).property
    change ‖((↑(unit⁻¹) : Integers K) : K)‖ ≤ 1 at inverse_bound
    change ‖((unit : Integers K) : K)‖ ≤ 1 at unit_bound
    have product_norm :
        ‖((unit : Integers K) : K)‖ * ‖((↑(unit⁻¹) : Integers K) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul]
      simp
    nlinarith [norm_nonneg ((unit : Integers K) : K),
      mul_le_mul_of_nonneg_left inverse_bound (norm_nonneg ((unit : Integers K) : K))]
  have order_eq : localDifferentOrder (p := p) (L := K) = order := by
    change (IsDiscreteValuationRing.addVal (Integers K)
      (localDifferentGenerator (p := p) (L := K))).toNat = order
    rw [IsDiscreteValuationRing.addVal_def _ unit irreducible order generator_eq, ENat.toNat_coe]
  rw [generator_eq, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, unit_norm, one_mul,
    norm_uniformizer_eq_prime_rpow_inv_ramificationExponent (p := p) uniformizer irreducible,
    localDifferentPaperOrder, order_eq]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The `d_i` used by Step(v) equals the actual normalized different order. -/
theorem localNormOrder_differentGenerator_eq_paperOrder :
    localNormOrder p (localDifferentGenerator (p := p) (L := K) : K) =
      localDifferentPaperOrder (p := p) (L := K) := by
  have prime_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have log_prime_ne_zero : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt))
  rw [localNormOrder, norm_differentGenerator_eq_prime_rpow_neg_paperOrder,
    Real.log_rpow prime_pos]
  field_simp

variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [NormedAlgebra K L] [IsScalarTower ℚ_[p] K L]

/-- Proposition 1.3(ii) directly bounds the different-generator orders in Step(v). -/
theorem localNormOrder_differentGenerator_le_degree_padicVal :
    localNormOrder p (localDifferentGenerator (p := p) (L := L) : L) ≤
      localNormOrder p (localDifferentGenerator (p := p) (L := K) : K) +
        padicValNat p (Module.finrank K L) +
        1 / (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
  simpa only [localNormOrder_differentGenerator_eq_paperOrder] using
    (localDifferentPaperOrder_le_degree_padicVal (p := p) (K := K) (L := L))

end LeanFormal.IUT.LocalDifferentNormOrder
