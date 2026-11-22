import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Integral scalar closure of the logarithmic shell

Compactness and density of the natural numbers in the p-adic integers extend
the additive subgroup's closure under natural multiples to integral scalars.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

/-- The integral logarithmic shell is closed under multiplication by p-adic integers. -/
theorem integralLogShell_padicInt_mul_mem
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (z : ℤ_[p]) {x : K} (hx : x ∈ integralLogShell (K := K) (p := p)) :
    algebraMap ℚ_[p] K (z : ℚ_[p]) * x ∈ integralLogShell (K := K) (p := p) := by
  refine DenseRange.induction_on (PadicInt.denseRange_natCast (p := p)) z ?_ ?_
  · exact (isCompact_integralLogShell (K := K) (p := p)).isClosed.preimage
      (((continuous_algebraMap ℚ_[p] K).comp continuous_subtype_val).mul continuous_const)
  · intro n
    simpa only [PadicInt.coe_natCast, map_natCast, nsmul_eq_mul] using
      (integralLogShell (K := K) (p := p)).nsmul_mem hx n

end LeanFormal.IUT.LocalFieldLogarithm
