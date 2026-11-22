import LeanFormal.IUT.Foundations.LocalFields.ClosedIntegralUnitCongruence
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse

/-!
# The actual small-unit congruence logarithm is the integer ring

For p*=p at odd p and p*=4 at p=2, the closed unit congruence ball of
radius norm(p*) maps isomorphically to O under (p*)^-1 log. The inverse
uses the proved Banach construction with its actual offset norm bound.
This identifies the small subgroup needed for the log-shell index.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

def logShellCongruenceUnits : Subgroup (Integers K)ˣ :=
  principalUnitsAtClosedRadius ‖(logShellScale p : K)‖ (norm_nonneg _)

omit [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K] localNormedAlgebra in
theorem norm_logShellScale_pos : 0 < ‖(logShellScale p : K)‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (logShellScale_pos (p := p)).ne')

omit [CompleteSpace K] [ProperSpace K] localNormedAlgebra in
theorem isOpen_logShellCongruenceUnits :
    IsOpen (logShellCongruenceUnits (K := K) (p := p) : Set (Integers K)ˣ) :=
  isOpen_principalUnitsAtClosedRadius _ (norm_logShellScale_pos (K := K) (p := p))

omit [CompleteSpace K] localNormedAlgebra in
theorem finite_logShellCongruenceQuotient :
    Finite ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) :=
  finite_principalUnitsAtClosedRadius_quotient _ (norm_logShellScale_pos (K := K) (p := p))

omit [CharZero K] [CompleteSpace K] [ProperSpace K] in
theorem logShellCongruenceUnits_le_principalUnits :
    logShellCongruenceUnits (K := K) (p := p) ≤ principalUnits := by
  intro u hu
  apply (mem_principalUnits_iff _).mpr
  exact (show ‖(u.val : K) - 1‖ ≤ ‖(logShellScale p : K)‖ from hu).trans_lt
    ((norm_logShellScale_lt_half (K := K) (p := p)).trans (by norm_num))

theorem norm_unitLog_le_scale_of_mem_congruence (u : (Integers K)ˣ)
    (hu : u ∈ logShellCongruenceUnits (K := K) (p := p)) :
    ‖unitLog u‖ ≤ ‖(logShellScale p : K)‖ := by
  let r := ‖(logShellScale p : K)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hrhalf : r < 1 / 2 := norm_logShellScale_lt_half (K := K) (p := p)
  have hx : ‖(u.val : K) - 1‖ ≤ r := hu
  have hrem := norm_logRemainder_sub_le (p := p) ((u.val : K) - 1) 0 hr hrhalf.le hx
    (by simpa using hr)
  have hzero : logRemainder (0 : K) = 0 := by simp [logRemainder, log1p_zero]
  rw [hzero, sub_zero, sub_zero] at hrem
  have hbound : ‖logRemainder ((u.val : K) - 1)‖ ≤ r :=
    hrem.trans ((mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hx)
  rw [unitLog_eq_log1p (p := p) u (logShellCongruenceUnits_le_principalUnits hu)]
  have heq : log1p ((u.val : K) - 1) =
      logRemainder ((u.val : K) - 1) + ((u.val : K) - 1) := by
    simp only [logRemainder]
    ring
  rw [heq]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbound hx)

theorem scaledUnitLog_mem_integers_of_mem_congruence (u : (Integers K)ˣ)
    (hu : u ∈ logShellCongruenceUnits (K := K) (p := p)) :
    (logShellScale p : K)⁻¹ * unitLog u ∈ Integers K := by
  apply (mem_integers_iff _).mpr
  have hbound := norm_unitLog_le_scale_of_mem_congruence (p := p) u hu
  have hquot : ‖unitLog u‖ / ‖(logShellScale p : K)‖ ≤ 1 :=
    (div_le_iff₀ (norm_logShellScale_pos (K := K) (p := p))).mpr (by simpa using hbound)
  simpa only [norm_mul, norm_inv, div_eq_mul_inv, mul_comm] using hquot

theorem unitLog_eq_zero_iff_one_of_mem_congruence (u : (Integers K)ˣ)
    (hu : u ∈ logShellCongruenceUnits (K := K) (p := p)) : unitLog u = 0 ↔ u = 1 := by
  constructor
  · intro hzero
    have hlog : log1p ((u.val : K) - 1) = 0 := by
      rw [← unitLog_eq_log1p (p := p) u (logShellCongruenceUnits_le_principalUnits hu), hzero]
    have hoffset := (log1p_eq_zero_iff_of_norm_le (p := p)
      (norm_nonneg _) (norm_logShellScale_lt_half (K := K) (p := p)) hu).mp hlog
    apply Units.ext
    apply Subtype.ext
    exact sub_eq_zero.mp hoffset
  · rintro rfl
    exact unitLog_one (p := p)

theorem exists_congruenceUnitLog_eq_scale_mul (x : Integers K) :
    ∃ u : (Integers K)ˣ, u ∈ logShellCongruenceUnits (K := K) (p := p) ∧
      unitLog u = (logShellScale p : K) * (x : K) := by
  have hrhalf := norm_logShellScale_lt_half (K := K) (p := p)
  have hy : ‖(logShellScale p : K) * (x : K)‖ ≤ ‖(logShellScale p : K)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_integers_iff _).mp x.property)
  obtain ⟨t, ht, hlog⟩ := exists_log1p_preimage (p := p) (norm_nonneg _) hrhalf _ hy
  have htone : ‖t‖ < 1 := ht.trans_lt (hrhalf.trans (by norm_num))
  let u := unitOfNormOne (K := K) ⟨1 + t, norm_one_add_of_norm_lt_one t htone⟩
  have hoffset : (u.val : K) - 1 = t := by change (1 + t) - 1 = t; ring
  have hu : u ∈ logShellCongruenceUnits (K := K) (p := p) := by
    change ‖(u.val : K) - 1‖ ≤ ‖(logShellScale p : K)‖
    rw [hoffset]
    exact ht
  exact ⟨u, hu, by
    rw [unitLog_eq_log1p (p := p) u (logShellCongruenceUnits_le_principalUnits hu), hoffset, hlog]⟩

def logShellCongruenceLogHom :
    logShellCongruenceUnits (K := K) (p := p) →* Multiplicative (Integers K) where
  toFun u := Multiplicative.ofAdd ⟨(logShellScale p : K)⁻¹ * unitLog u.val,
    scaledUnitLog_mem_integers_of_mem_congruence u.val u.property⟩
  map_one' := by
    apply Subtype.ext
    change (logShellScale p : K)⁻¹ * unitLog (1 : (Integers K)ˣ) = 0
    rw [unitLog_one (p := p), mul_zero]
  map_mul' u v := by
    apply Subtype.ext
    change (logShellScale p : K)⁻¹ * unitLog (u.val * v.val) =
      (logShellScale p : K)⁻¹ * unitLog u.val + (logShellScale p : K)⁻¹ * unitLog v.val
    rw [unitLog_mul (p := p), mul_add]

theorem logShellCongruenceLogHom_injective :
    Function.Injective (logShellCongruenceLogHom (K := K) (p := p)) := by
  intro u v h
  have hscaled := congrArg (fun z : Multiplicative (Integers K) =>
    ((Multiplicative.toAdd z : Integers K) : K)) h
  have hscale : (logShellScale p : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (logShellScale_pos (p := p)).ne'
  have hlog : unitLog u.val = unitLog v.val := mul_left_cancel₀ (inv_ne_zero hscale) hscaled
  have hsmall : u.val * v.val⁻¹ ∈ logShellCongruenceUnits (K := K) (p := p) :=
    (logShellCongruenceUnits (K := K) (p := p)).mul_mem u.property
      ((logShellCongruenceUnits (K := K) (p := p)).inv_mem v.property)
  have hzero : unitLog (u.val * v.val⁻¹) = 0 := by
    rw [unitLog_mul (p := p), unitLog_inv (p := p), hlog, add_neg_cancel]
  apply Subtype.ext
  exact mul_inv_eq_one.mp ((unitLog_eq_zero_iff_one_of_mem_congruence _ hsmall).mp hzero)

theorem logShellCongruenceLogHom_surjective :
    Function.Surjective (logShellCongruenceLogHom (K := K) (p := p)) := by
  intro x
  obtain ⟨u, hu, hlog⟩ := exists_congruenceUnitLog_eq_scale_mul (p := p) (Multiplicative.toAdd x)
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  change (logShellScale p : K)⁻¹ * unitLog u = ((Multiplicative.toAdd x : Integers K) : K)
  rw [hlog, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (logShellScale_pos (p := p)).ne')]

def logShellCongruenceLogEquiv :
    logShellCongruenceUnits (K := K) (p := p) ≃* Multiplicative (Integers K) :=
  MulEquiv.ofBijective (logShellCongruenceLogHom (K := K) (p := p))
    ⟨logShellCongruenceLogHom_injective, logShellCongruenceLogHom_surjective⟩

end

end LeanFormal.IUT.LocalFieldLogarithm
