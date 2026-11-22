import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitCongruence
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInjectivity
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The kernel of the actual full-unit logarithm

A finite small-congruence quotient sends any zero-logarithm unit to the
ball where the actual analytic logarithm is injective. Hence its power
is one. Conversely the logarithm kills torsion by the proved power law
and characteristic zero. The resulting torsion quotient therefore has
a constructed injective logarithm, not a postulated kernel comparison.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

theorem unitLog_eq_zero_iff_exists_pow_eq_one (u : (Integers K)ˣ) :
    unitLog u = 0 ↔ ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  constructor
  · intro hu
    obtain ⟨n, hn, hsmall⟩ := exists_uniform_smallUnit_exponent (K := K) (1 / 4) (by norm_num)
    have hprincipal : u ^ n ∈ principalUnits :=
      (mem_principalUnits_iff _).mpr ((hsmall u).trans (by norm_num))
    have hlog : log1p (((u ^ n).val : K) - 1) = 0 := by
      rw [← unitLog_eq_log1p (p := p) _ hprincipal, unitLog_pow (p := p), hu, mul_zero]
    have hzero : ((u ^ n).val : K) - 1 = 0 :=
      (log1p_eq_zero_iff_of_norm_le (p := p) (r := 1 / 4)
        (by norm_num) (by norm_num) (hsmall u).le).mp hlog
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  · rintro ⟨n, hn, hpow⟩
    have h := unitLog_pow (p := p) u n
    rw [hpow, unitLog_one (p := p)] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Nat.cast_ne_zero.mpr (ne_of_gt hn))

theorem unitLog_eq_zero_iff_isOfFinOrder (u : (Integers K)ˣ) :
    unitLog u = 0 ↔ IsOfFinOrder u := by
  rw [unitLog_eq_zero_iff_exists_pow_eq_one (p := p), isOfFinOrder_iff_pow_eq_one]

theorem unitLogHom_ker_eq_torsion :
    (unitLogHom (K := K) (p := p)).ker = CommGroup.torsion (Integers K)ˣ := by
  ext u
  change unitLog u = 0 ↔ IsOfFinOrder u
  exact unitLog_eq_zero_iff_isOfFinOrder (p := p) u

/-- The induced logarithm on the actual quotient by all torsion units. -/
def unitLogTorsionQuotientHom :
    ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) →* Multiplicative K :=
  QuotientGroup.lift _ (unitLogHom (p := p)) (by
    intro u hu
    change unitLog u = 0
    exact (unitLog_eq_zero_iff_isOfFinOrder (p := p) u).mpr hu)

theorem unitLogTorsionQuotientHom_mk (u : (Integers K)ˣ) :
    unitLogTorsionQuotientHom (p := p) (QuotientGroup.mk u) =
      Multiplicative.ofAdd (unitLog u) := rfl

theorem unitLogTorsionQuotientHom_injective :
    Function.Injective (unitLogTorsionQuotientHom (K := K) (p := p)) := by
  intro a b
  refine Quotient.inductionOn₂' a b ?_
  intro u v h
  change unitLogHom (p := p) u = unitLogHom (p := p) v at h
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply, ← unitLogHom_ker_eq_torsion (p := p),
    MonoidHom.mem_ker, map_mul, map_inv, ← h, inv_mul_cancel]

/-- The torsion quotient is genuinely isomorphic to the logarithmic image. -/
def unitLogTorsionQuotientEquivRange :
    ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) ≃*
      (unitLogHom (K := K) (p := p)).range := by
  let f := unitLogHom (K := K) (p := p)
  let rangeHom : ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) →* f.range :=
    QuotientGroup.lift _ f.rangeRestrict (by
      intro u hu
      apply Subtype.ext
      change unitLog u = 0
      exact (unitLog_eq_zero_iff_isOfFinOrder (p := p) u).mpr hu)
  apply MulEquiv.ofBijective rangeHom
  constructor
  · intro a b
    refine Quotient.inductionOn₂' a b ?_
    intro u v h
    have hlog : f u = f v := congrArg Subtype.val h
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, ← unitLogHom_ker_eq_torsion (K := K) (p := p),
      MonoidHom.mem_ker, map_mul, map_inv, ← hlog, inv_mul_cancel]
  · rintro ⟨y, u, rfl⟩
    exact ⟨QuotientGroup.mk u, rfl⟩

end

end LeanFormal.IUT.LocalFieldLogarithm
