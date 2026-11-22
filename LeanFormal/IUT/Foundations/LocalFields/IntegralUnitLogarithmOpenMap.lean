import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmQuotientTopology
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse

/-!
# The actual local unit logarithm is open

The scaled logarithmic image contains the valuation integers and is an
additive subgroup, hence open. The unscaled image is open as well. The
actual torsion quotient topology then proves openness of the logarithm.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

theorem isOpen_integralLogShell : IsOpen (integralLogShell (K := K) (p := p) : Set K) := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  refine ⟨1, zero_lt_one, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hmem : y - x ∈ integralLogShell (K := K) (p := p) :=
    integers_subset_integralLogShell (p := p) ((mem_integers_iff _).mpr hnorm.le)
  change y ∈ integralLogShell (K := K) (p := p)
  simpa only [sub_add_cancel] using (integralLogShell (K := K) (p := p)).add_mem hmem hx

theorem isOpen_unitLog_range : IsOpen (Set.range (unitLog (K := K))) := by
  have hc : (logShellScale p : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))
  have hrange : Set.range (unitLog (K := K)) =
      (fun x : K => (logShellScale p : K)⁻¹ * x) ⁻¹'
        (integralLogShell (K := K) (p := p) : Set K) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, mul_left_cancel₀ (inv_ne_zero hc) hu⟩
  rw [hrange]
  exact (isOpen_integralLogShell (p := p)).preimage (continuous_const.mul continuous_id)

theorem isOpen_unitLogHom_range :
    IsOpen ((unitLogHom (K := K) (p := p)).range : Set (Multiplicative K)) :=
  isOpen_unitLog_range (K := K) (p := p)

theorem isOpenMap_unitLog : IsOpenMap (unitLog (K := K)) := by
  have hq : IsOpenMap (QuotientGroup.mk : (Integers K)ˣ →
      (Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) := QuotientGroup.isOpenMap_coe
  have hh := (unitLogTorsionQuotientHomeomorph (K := K) (p := p)).isOpenMap
  have hi := (isOpen_unitLogHom_range (K := K) (p := p)).isOpenMap_subtype_val
  have hcomp := hi.comp (hh.comp hq)
  change IsOpenMap (unitLog (K := K)) at hcomp
  exact hcomp

end

end LeanFormal.IUT.LocalFieldLogarithm
