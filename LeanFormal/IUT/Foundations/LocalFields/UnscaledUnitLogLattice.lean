import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice

/-!
# The unscaled unit-log lattice

IUT IV Proposition 1.2 uses the unscaled image `log_p(R_i^×)`.  The repository's
`integralLogShellLattice` is the scaled image `(p*)^{-1} log(R_i^×)`.  This file
defines the actual unscaled image as a `Zp`-submodule and records its basic
lattice properties.

The definition is made through the equivalent scaled lattice
`(logShellScale p) • integralLogShellLattice`; the carrier is then proved equal
to `Set.range unitLog`.  This avoids inventing a scalar-closure field: scalar
closure is transported from the already proved closure of the scaled shell.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
open scoped Pointwise

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

/-- Multiplication by the paper's scalar `p*` on the local field, viewed as a
`Zp`-linear endomorphism. -/
def unitLogScaleMul : K →ₗ[ℤ_[p]] K :=
  (LinearMap.mulLeft ℚ_[p] (logShellScale p : K)).restrictScalars ℤ_[p]

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K] in
@[simp] theorem unitLogScaleMul_apply (x : K) :
    unitLogScaleMul (K := K) (p := p) x = (logShellScale p : K) * x := by
  rfl

/-- The actual unscaled unit-log image, as a `Zp`-submodule.  It is defined as
`p* • I`, where `I` is the existing scaled shell; the next theorem identifies
its carrier with `Set.range unitLog`. -/
def unitLogLattice : Submodule ℤ_[p] K :=
  (integralLogShellLattice (K := K) (p := p)).map
    (unitLogScaleMul (K := K) (p := p))

theorem coe_unitLogLattice_eq_scale_smul :
    (unitLogLattice (K := K) (p := p) : Set K) =
      (logShellScale p : K) • (integralLogShellLattice (K := K) (p := p) : Set K) := by
  ext x
  constructor
  · intro hx
    change x ∈ (unitLogLattice (K := K) (p := p) : Set K) at hx
    rw [unitLogLattice] at hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_map (f := unitLogScaleMul (K := K) (p := p))).mp hx
    exact ⟨y, hy, (unitLogScaleMul_apply (p := p) y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    change (unitLogScaleMul (K := K) (p := p) y) ∈
      (unitLogLattice (K := K) (p := p) : Set K)
    rw [unitLogLattice]
    exact (Submodule.mem_map (f := unitLogScaleMul (K := K) (p := p))).mpr
      ⟨y, hy, unitLogScaleMul_apply (p := p) y⟩

theorem coe_unitLogLattice_eq_range :
    (unitLogLattice (K := K) (p := p) : Set K) =
      Set.range (unitLog (K := K)) := by
  rw [coe_unitLogLattice_eq_scale_smul]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    have hs : (logShellScale p : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  · rintro ⟨u, rfl⟩
    refine ⟨(logShellScale p : K)⁻¹ * unitLog (K := K) u, ⟨u, rfl⟩, ?_⟩
    have hs : (logShellScale p : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem mem_unitLogLattice_iff {x : K} :
    x ∈ unitLogLattice (K := K) (p := p) ↔
      x ∈ Set.range (unitLog (K := K)) := by
  change x ∈ (unitLogLattice (K := K) (p := p) : Set K) ↔
    x ∈ Set.range (unitLog (K := K))
  rw [coe_unitLogLattice_eq_range]

theorem isCompact_unitLogLattice :
    IsCompact (unitLogLattice (K := K) (p := p) : Set K) := by
  rw [coe_unitLogLattice_eq_range]
  exact isCompact_unitLog_range (K := K) (p := p)

theorem unitLogLattice_le_integralLogShellLattice :
    unitLogLattice (K := K) (p := p) ≤
      integralLogShellLattice (K := K) (p := p) := by
  intro x hx
  rw [mem_unitLogLattice_iff] at hx
  rcases hx with ⟨u, rfl⟩
  let y : K := (logShellScale p : K)⁻¹ * unitLog (K := K) u
  have hy : y ∈ integralLogShellLattice (K := K) (p := p) := ⟨u, rfl⟩
  have hz : (logShellScale p) • y ∈
      integralLogShellLattice (K := K) (p := p) :=
    (integralLogShellLattice (K := K) (p := p)).nsmul_mem hy (logShellScale p)
  rw [nsmul_eq_mul] at hz
  change (logShellScale p : K) * ((logShellScale p : K)⁻¹ * unitLog (K := K) u) ∈
    integralLogShellLattice (K := K) (p := p) at hz
  have hs : (logShellScale p : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul] at hz
  exact hz

variable [FiniteDimensional ℚ_[p] K]

instance unitLogLatticeFinite : Module.Finite ℤ_[p] (unitLogLattice (K := K) (p := p)) :=
  finite_of_isCompact (p := p) _ (isCompact_unitLogLattice (K := K) (p := p))

instance unitLogLatticeFree : Module.Free ℤ_[p] (unitLogLattice (K := K) (p := p)) :=
  free_of_isCompact (p := p) _ (isCompact_unitLogLattice (K := K) (p := p))

end

end LeanFormal.IUT.LocalFieldLogarithm
