import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmRationalization
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# The actual local Galois action on unit perfection

On an algebraic Qp extension, algebra automorphisms preserve the spectral
norm. They therefore act on the actual integer units. The constructed
logarithm is equivariant, and the action on the rationalized group agrees
on actual unit generators with this original action.
Absolute-Galois and ind-limit identifications are subsequent steps.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
variable [Algebra.IsAlgebraic ℚ_[p] K]

theorem norm_localGalois_eq (σ : K ≃ₐ[ℚ_[p]] K) (x : K) : ‖σ x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p], NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem isometry_localGalois (σ : K ≃ₐ[ℚ_[p]] K) : Isometry σ := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_localGalois_eq]

variable [IsUltrametricDist K]

def localGaloisUnitMap (σ : K ≃ₐ[ℚ_[p]] K) : (Integers K)ˣ →* (Integers K)ˣ :=
  integralUnitMap σ.toRingHom (isometry_localGalois σ)

theorem localGaloisUnitMap_one (u : (Integers K)ˣ) :
    localGaloisUnitMap (1 : K ≃ₐ[ℚ_[p]] K) u = u := by
  apply Units.ext
  apply Subtype.ext
  rfl

theorem localGaloisUnitMap_mul (σ τ : K ≃ₐ[ℚ_[p]] K) (u : (Integers K)ˣ) :
    localGaloisUnitMap (σ * τ) u = localGaloisUnitMap σ (localGaloisUnitMap τ u) := by
  apply Units.ext
  apply Subtype.ext
  rfl

instance localUnitGaloisMulAction : MulAction (K ≃ₐ[ℚ_[p]] K) (Integers K)ˣ where
  smul σ u := localGaloisUnitMap σ u
  one_smul u := localGaloisUnitMap_one (K := K) (p := p) u
  mul_smul := localGaloisUnitMap_mul

variable [CharZero K] [CompleteSpace K] [ProperSpace K]

theorem unitLog_localGalois_smul (σ : K ≃ₐ[ℚ_[p]] K) (u : (Integers K)ˣ) :
    unitLog (σ • u) = σ (unitLog u) := by
  change unitLog (localGaloisUnitMap σ u) = σ (unitLog u)
  exact (unitLog_map (p := p) σ.toRingHom (isometry_localGalois σ) u).symm

instance unitLogPerfectionGaloisMulAction : MulAction (K ≃ₐ[ℚ_[p]] K) (UnitLogPerfection K) where
  smul σ x := (unitLogPerfectionEquiv (p := p)).symm (σ (unitLogPerfectionEquiv (p := p) x))
  one_smul x := by
    change (unitLogPerfectionEquiv (p := p)).symm (unitLogPerfectionEquiv (p := p) x) = x
    exact (unitLogPerfectionEquiv (p := p)).symm_apply_apply x
  mul_smul σ τ x := by
    change (unitLogPerfectionEquiv (p := p)).symm ((σ * τ) (unitLogPerfectionEquiv (p := p) x)) =
      (unitLogPerfectionEquiv (p := p)).symm (σ (unitLogPerfectionEquiv (p := p)
        ((unitLogPerfectionEquiv (p := p)).symm (τ (unitLogPerfectionEquiv (p := p) x)))))
    rw [LinearEquiv.apply_symm_apply]
    rfl

omit [Algebra.IsAlgebraic ℚ_[p] K] in
theorem unitLogPerfectionEquiv_localGalois_smul (σ : K ≃ₐ[ℚ_[p]] K) (x : UnitLogPerfection K) :
    unitLogPerfectionEquiv (p := p) (σ • x) = σ (unitLogPerfectionEquiv (p := p) x) :=
  (unitLogPerfectionEquiv (p := p)).apply_symm_apply _

/-- The action is compatible with actual unit generators, rather than
only an unrelated transported field action on an abstract vector space. -/
theorem unitLogPerfection_mk_localGalois_smul (σ : K ≃ₐ[ℚ_[p]] K) (u : (Integers K)ˣ) :
    σ • (LocalizedModule.mk (Additive.ofMul u) 1 : UnitLogPerfection K) =
      LocalizedModule.mk (Additive.ofMul (σ • u)) 1 := by
  apply (unitLogPerfectionEquiv (p := p)).injective
  rw [unitLogPerfectionEquiv_localGalois_smul, unitLogPerfectionEquiv_mk_one,
    unitLogPerfectionEquiv_mk_one, unitLog_localGalois_smul]

end

end LeanFormal.IUT.LocalFieldLogarithm
