import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitFiniteCarrier
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeriesTransport

/-!
# Logarithms of actual units in an algebraic Qp extension

Each unit is evaluated in its finite complete carrier. Equality of the
result for any two local-field presentations follows by using a common
positive exponent in the analytic logarithm formula. The ambient field
need not be complete or locally compact.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

section Presentations

variable {F E Ω : Type*} [NormedField F] [NormedField E] [NormedField Ω]
variable [IsUltrametricDist F] [IsUltrametricDist E] [IsUltrametricDist Ω]
variable [CharZero F] [CompleteSpace F] [ProperSpace F]
variable [CharZero E] [CompleteSpace E] [ProperSpace E]
variable {p : ℕ} [Fact p.Prime]
variable [sourceNormedAlgebra : NormedAlgebra ℚ_[p] F]
variable [otherNormedAlgebra : NormedAlgebra ℚ_[p] E]

include sourceNormedAlgebra in
theorem unitLog_map_eq_withExponent (e : F →+* Ω) (he : Isometry e)
    (u : (Integers F)ˣ) {n : ℕ} (hn : n ≠ 0) (hu : u ^ n ∈ principalUnits) :
    e (unitLog u) = unitLogWithExponent n (integralUnitMap e he u) := by
  rw [unitLog_eq_withExponent (p := p) u hn hu]
  have hoffset : (((integralUnitMap e he u) ^ n).val : Ω) - 1 =
      e (((u ^ n).val : F) - 1) := by
    rw [← map_pow, integralUnitMap_val, map_sub, map_one]
  dsimp only [unitLogWithExponent]
  rw [map_div₀, map_natCast, hoffset,
    log1p_map_of_continuous (p := p) e he.continuous _
      ((mem_principalUnits_iff _).mp hu)]

include sourceNormedAlgebra otherNormedAlgebra in
theorem unitLog_map_eq_of_unitMap_eq
    (e : F →+* Ω) (he : Isometry e) (f : E →+* Ω) (hf : Isometry f)
    (u : (Integers F)ˣ) (v : (Integers E)ˣ)
    (huv : integralUnitMap e he u = integralUnitMap f hf v) :
    e (unitLog u) = f (unitLog v) := by
  let n := integralUnitExponent (K := F)
  let m := integralUnitExponent (K := E)
  have hn : n ≠ 0 := ne_of_gt integralUnitExponent_pos
  have hm : m ≠ 0 := ne_of_gt integralUnitExponent_pos
  have hun : u ^ (n * m) ∈ principalUnits := by
    rw [pow_mul]
    exact (principalUnits (K := F)).pow_mem (pow_integralUnitExponent_mem u) m
  have hvm : v ^ (n * m) ∈ principalUnits := by
    rw [Nat.mul_comm, pow_mul]
    exact (principalUnits (K := E)).pow_mem (pow_integralUnitExponent_mem v) n
  rw [unitLog_map_eq_withExponent (p := p) e he u (Nat.mul_ne_zero hn hm) hun,
    unitLog_map_eq_withExponent (p := p) f hf v (Nat.mul_ne_zero hn hm) hvm, huv]

end Presentations

variable {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]
variable [Algebra.IsAlgebraic ℚ_[p] Ω]

omit [Algebra.IsAlgebraic ℚ_[p] Ω] [IsUltrametricDist Ω] in
theorem isometry_intermediateField_inclusion (F : IntermediateField ℚ_[p] Ω) :
    Isometry F.val.toRingHom := Isometry.of_dist_eq (fun _ _ => rfl)

def algebraicUnitLog (u : (Integers Ω)ˣ) : Ω :=
  (finiteUnitField (p := p) u).val.toRingHom (unitLog (finiteUnitLift (p := p) u))

omit [Algebra.IsAlgebraic ℚ_[p] Ω] in
theorem finiteUnitLift_map (u : (Integers Ω)ˣ) :
    integralUnitMap (finiteUnitField (p := p) u).val.toRingHom
      (isometry_intermediateField_inclusion _)
      (finiteUnitLift (p := p) u) = u := by
  apply Units.ext
  apply Subtype.ext
  exact finiteUnitLift_val (p := p) u

theorem algebraicUnitLog_eq_map
    {F : Type*} [NormedField F] [IsUltrametricDist F]
    [CharZero F] [CompleteSpace F] [ProperSpace F] [NormedAlgebra ℚ_[p] F]
    (e : F →+* Ω) (he : Isometry e) (v : (Integers F)ˣ) :
    algebraicUnitLog (p := p) (integralUnitMap e he v) = e (unitLog v) := by
  exact unitLog_map_eq_of_unitMap_eq (p := p)
    (finiteUnitField (p := p) (integralUnitMap e he v)).val.toRingHom
    (isometry_intermediateField_inclusion _)
    e he _ v (finiteUnitLift_map _)

theorem algebraicUnitLog_eq_log1p (u : (Integers Ω)ˣ)
    (hu : ‖(u.val : Ω) - 1‖ < 1) :
    algebraicUnitLog (p := p) u = log1p ((u.val : Ω) - 1) := by
  let F := finiteUnitField (p := p) u
  let v := finiteUnitLift (p := p) u
  have hval : F.val.toRingHom (v.val : F) = (u.val : Ω) := finiteUnitLift_val (p := p) u
  have hv : v ∈ principalUnits := by
    apply (mem_principalUnits_iff _).mpr
    change ‖(v.val : F) - 1‖ < 1
    rw [← norm_map_of_isometry F.val.toRingHom (isometry_intermediateField_inclusion F),
      map_sub, map_one, hval]
    exact hu
  change F.val.toRingHom (unitLog v) = _
  rw [unitLog_eq_log1p (p := p) v hv,
    log1p_map_of_continuous (p := p) F.val.toRingHom
      (isometry_intermediateField_inclusion F).continuous _
      ((mem_principalUnits_iff _).mp hv), map_sub, map_one, hval]

theorem algebraicUnitLog_eq_zero_iff_isOfFinOrder (u : (Integers Ω)ˣ) :
    algebraicUnitLog (p := p) u = 0 ↔ IsOfFinOrder u := by
  let F := finiteUnitField (p := p) u
  let v := finiteUnitLift (p := p) u
  have hinj : Function.Injective
      (integralUnitMap F.val.toRingHom (isometry_intermediateField_inclusion F)) := by
    intro a b hab
    apply Units.ext
    apply Subtype.ext
    exact Subtype.val_injective (congrArg (fun w : (Integers Ω)ˣ => (w.val : Ω)) hab)
  change F.val.toRingHom (unitLog v) = 0 ↔ _
  rw [map_eq_zero_iff F.val.toRingHom F.val.toRingHom.injective]
  have horder : IsOfFinOrder
      (integralUnitMap F.val.toRingHom (isometry_intermediateField_inclusion F) v) ↔
      IsOfFinOrder v := Function.Injective.isOfFinOrder_iff
    (f := integralUnitMap F.val.toRingHom (isometry_intermediateField_inclusion F)) hinj
  rw [finiteUnitLift_map] at horder
  have hlog : unitLog (K := F) v = 0 ↔ IsOfFinOrder v :=
    unitLog_eq_zero_iff_isOfFinOrder (K := F) (p := p) v
  exact ⟨fun h => horder.symm.mp (hlog.mp h),
    fun h => hlog.mpr (horder.mp h)⟩

end

end LeanFormal.IUT.LocalFieldLogarithm
