import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmCongruenceEquiv

/-!
# Finiteness of the actual local integral torsion units

The actual full logarithm kills exactly torsion. Its restriction to the
closed p*-congruence subgroup has trivial kernel. Torsion therefore embeds
in the already proved finite congruence quotient of the actual unit group.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

def torsionCongruenceHom :
    CommGroup.torsion (Integers K)ˣ →*
      ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) :=
  (QuotientGroup.mk' (logShellCongruenceUnits (K := K) (p := p))).comp
    (CommGroup.torsion (Integers K)ˣ).subtype

theorem torsionCongruenceHom_injective :
    Function.Injective (torsionCongruenceHom (K := K) (p := p)) := by
  intro u v h
  have hsmall : u.val * v.val⁻¹ ∈ logShellCongruenceUnits (K := K) (p := p) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change torsionCongruenceHom (p := p) u * (torsionCongruenceHom (p := p) v)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hu : unitLog u.val = 0 :=
    (unitLog_eq_zero_iff_isOfFinOrder (p := p) u.val).mpr u.property
  have hv : unitLog v.val = 0 :=
    (unitLog_eq_zero_iff_isOfFinOrder (p := p) v.val).mpr v.property
  have hzero : unitLog (u.val * v.val⁻¹) = 0 := by
    rw [unitLog_mul (p := p), unitLog_inv (p := p), hu, hv, neg_zero, add_zero]
  apply Subtype.ext
  exact mul_inv_eq_one.mp ((unitLog_eq_zero_iff_one_of_mem_congruence _ hsmall).mp hzero)

include localNormedAlgebra in
theorem finite_integralUnitTorsion : Finite (CommGroup.torsion (Integers K)ˣ) := by
  letI := finite_logShellCongruenceQuotient (K := K) (p := p)
  exact Finite.of_injective (torsionCongruenceHom (K := K) (p := p))
    torsionCongruenceHom_injective

end

end LeanFormal.IUT.LocalFieldLogarithm
