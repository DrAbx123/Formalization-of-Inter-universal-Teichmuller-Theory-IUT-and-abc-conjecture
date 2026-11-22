import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm

/-!
# Functoriality of the actual integral-unit logarithm

The field map induces maps of the actual integer rings and their units.
Commutation with the analytic series and independence of the powering
exponent then prove equivariance of the full logarithm and its scaled
image. This supplies actual maps for local Galois actions, rather than
an equivariance field on a source record.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
variable [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist K] [IsUltrametricDist L] in
theorem norm_map_of_isometry (e : K →+* L) (he : Isometry e) (x : K) :
    ‖e x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using he.dist_eq x 0

/-- The map of actual valuation-integer subrings induced by a field map. -/
def integralRingMap (e : K →+* L) (he : Isometry e) : Integers K →+* Integers L where
  toFun x := ⟨e (x : K), (mem_integers_iff _).mpr
    ((norm_map_of_isometry e he _).trans_le ((mem_integers_iff _).mp x.property))⟩
  map_zero' := Subtype.ext e.map_zero
  map_one' := Subtype.ext e.map_one
  map_add' x y := Subtype.ext (e.map_add x y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- The induced map on full actual integral unit groups. -/
def integralUnitMap (e : K →+* L) (he : Isometry e) : (Integers K)ˣ →* (Integers L)ˣ :=
  Units.map (integralRingMap e he).toMonoidHom

theorem integralUnitMap_val (e : K →+* L) (he : Isometry e) (u : (Integers K)ˣ) :
    ((integralUnitMap e he u).val : L) = e (u.val : K) := rfl

theorem integralUnitMap_mem_principalUnits (e : K →+* L) (he : Isometry e)
    (u : (Integers K)ˣ) (hu : u ∈ principalUnits) :
    integralUnitMap e he u ∈ principalUnits := by
  apply (mem_principalUnits_iff _).mpr
  rw [integralUnitMap_val, ← map_one e, ← map_sub, norm_map_of_isometry e he]
  exact (mem_principalUnits_iff _).mp hu

section Analytic

variable [CharZero K] [CompleteSpace K] [ProperSpace K]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable {p : ℕ} [Fact p.Prime]
variable [sourceNormedAlgebra : NormedAlgebra ℚ_[p] K]
variable [targetNormedAlgebra : NormedAlgebra ℚ_[p] L]

include sourceNormedAlgebra targetNormedAlgebra

/-- The full logarithm commutes with the actual unit map, even though its
chosen finite-quotient exponent may differ in the two fields. -/
theorem unitLog_map (e : K →+* L) (he : Isometry e) (u : (Integers K)ˣ) :
    e (unitLog u) = unitLog (integralUnitMap e he u) := by
  let n := integralUnitExponent (K := K)
  have hn : n ≠ 0 := ne_of_gt integralUnitExponent_pos
  have hu : u ^ n ∈ principalUnits := pow_integralUnitExponent_mem u
  have hpow : (integralUnitMap e he u) ^ n = integralUnitMap e he (u ^ n) :=
    (map_pow (integralUnitMap e he) u n).symm
  have hv : (integralUnitMap e he u) ^ n ∈ principalUnits := by
    rw [hpow]
    exact integralUnitMap_mem_principalUnits e he _ hu
  have hoffset : (((integralUnitMap e he u) ^ n).val : L) - 1 =
      e (((u ^ n).val : K) - 1) := by
    rw [hpow, integralUnitMap_val, map_sub, map_one]
  rw [unitLog_eq_withExponent (p := p) u hn hu,
    unitLog_eq_withExponent (p := p) (integralUnitMap e he u) hn hv]
  dsimp only [unitLogWithExponent]
  rw [map_div₀, map_natCast, hoffset,
    log1p_map (p := p) e he _ ((mem_principalUnits_iff _).mp hu)]

/-- The actual scaled logarithmic image is preserved under the field map. -/
theorem map_mem_integralLogShell (e : K →+* L) (he : Isometry e)
    {x : K} (hx : x ∈ integralLogShell (K := K) (p := p)) :
    e x ∈ integralLogShell (K := L) (p := p) := by
  obtain ⟨u, rfl⟩ := hx
  change ∃ v : (Integers L)ˣ, (logShellScale p : L)⁻¹ * unitLog v =
    e ((logShellScale p : K)⁻¹ * unitLog u)
  refine ⟨integralUnitMap e he u, ?_⟩
  rw [← unitLog_map (p := p) e he u, map_mul, map_inv₀, map_natCast]

end Analytic

end

end LeanFormal.IUT.LocalFieldLogarithm
