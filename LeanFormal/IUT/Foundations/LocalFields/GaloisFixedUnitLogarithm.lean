import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeriesTransport

/-!
# The logarithmic image of actual Galois-fixed original units

Descend the fixed original units to the actual base integer units and
apply the constructed logarithm. Its image is exactly the base logarithmic
image embedded in the algebraic extension, hence compact. This is the
pre-log-shell in III Definition 1.1, rather than the whole fixed field of
unit perfection. The upper field need not be complete or proper.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L]
variable [IsUltrametricDist K] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]
variable [IsScalarTower ℚ_[p] K L] [Algebra.IsAlgebraic ℚ_[p] L] [IsGalois K L]
variable [CharZero K] [CompleteSpace K] [ProperSpace K]

def galoisFixedUnitLog
    (u : localGaloisFixedIntegralUnits (K := K) (L := L) (p := p)) : L :=
  algebraMap K L (unitLog ((baseUnitsGaloisFixedEquiv (p := p)).symm u))

omit [CharZero K] [CompleteSpace K] in
theorem galoisFixedUnitLog_range :
    Set.range (galoisFixedUnitLog (K := K) (L := L) (p := p)) =
      (algebraMap K L) '' Set.range (unitLog (K := K)) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, ⟨(baseUnitsGaloisFixedEquiv (p := p)).symm u, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨baseUnitsGaloisFixedEquiv (L := L) (p := p) v, ?_⟩
    simp only [galoisFixedUnitLog, MulEquiv.symm_apply_apply]

theorem isCompact_galoisFixedUnitLog_range :
    IsCompact (Set.range (galoisFixedUnitLog (K := K) (L := L) (p := p))) := by
  rw [galoisFixedUnitLog_range]
  exact (isCompact_unitLog_range (p := p)).image
    (isometry_localField_algebraMap (K := K) (L := L)).continuous

/-- On actual principal fixed units, descent gives precisely the analytic
series in the original upper field, even if that field is not complete. -/
theorem galoisFixedUnitLog_eq_log1p
    (u : localGaloisFixedIntegralUnits (K := K) (L := L) (p := p))
    (hu : ‖(u.val.val : L) - 1‖ < 1) :
    galoisFixedUnitLog (p := p) u = log1p ((u.val.val : L) - 1) := by
  let v := (baseUnitsGaloisFixedEquiv (K := K) (L := L) (p := p)).symm u
  have hval : algebraMap K L (v.val : K) = (u.val.val : L) :=
    congrArg (fun w : localGaloisFixedIntegralUnits (K := K) (L := L) (p := p) =>
      (w.val.val : L)) ((baseUnitsGaloisFixedEquiv (p := p)).apply_symm_apply u)
  have hoffset : algebraMap K L ((v.val : K) - 1) = (u.val.val : L) - 1 := by
    rw [map_sub, map_one, hval]
  have hv : ‖(v.val : K) - 1‖ < 1 := by
    rw [← norm_algebraMap' L _, hoffset]
    exact hu
  change algebraMap K L (unitLog v) = _
  rw [unitLog_eq_log1p (p := p) v ((mem_principalUnits_iff _).mpr hv),
    log1p_map_of_continuous (p := p) (algebraMap K L)
      (isometry_localField_algebraMap (K := K) (L := L)).continuous _ hv, hoffset]

def galoisFixedLogShell : AddSubgroup L :=
  (integralLogShell (K := K) (p := p)).map (algebraMap K L).toAddMonoidHom

theorem galoisFixedLogShell_eq_fixedUnitLog_range :
    (galoisFixedLogShell (K := K) (L := L) (p := p) : Set L) =
      Set.range (fun u : localGaloisFixedIntegralUnits (K := K) (L := L) (p := p) =>
        (logShellScale p : L)⁻¹ * galoisFixedUnitLog (p := p) u) := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨baseUnitsGaloisFixedEquiv (L := L) (p := p) v, ?_⟩
    change (logShellScale p : L)⁻¹ *
      galoisFixedUnitLog (p := p) (baseUnitsGaloisFixedEquiv (p := p) v) =
      algebraMap K L ((logShellScale p : K)⁻¹ * unitLog v)
    simp only [galoisFixedUnitLog, MulEquiv.symm_apply_apply, map_mul, map_inv₀, map_natCast]
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨(baseUnitsGaloisFixedEquiv (p := p)).symm u, rfl⟩, ?_⟩
    change algebraMap K L ((logShellScale p : K)⁻¹ *
      unitLog ((baseUnitsGaloisFixedEquiv (p := p)).symm u)) = _
    simp only [galoisFixedUnitLog, map_mul, map_inv₀, map_natCast]

omit [IsUltrametricDist L] [NormedAlgebra ℚ_[p] L]
  [IsScalarTower ℚ_[p] K L] [Algebra.IsAlgebraic ℚ_[p] L] [IsGalois K L] in
theorem isCompact_galoisFixedLogShell :
    IsCompact (galoisFixedLogShell (K := K) (L := L) (p := p) : Set L) :=
  (isCompact_integralLogShell (K := K) (p := p)).image
    (isometry_localField_algebraMap (K := K) (L := L)).continuous

omit [IsUltrametricDist L] [NormedAlgebra ℚ_[p] L]
  [IsScalarTower ℚ_[p] K L] [Algebra.IsAlgebraic ℚ_[p] L] [IsGalois K L] in
theorem baseIntegers_image_subset_galoisFixedLogShell :
    (algebraMap K L) '' (Integers K : Set K) ⊆
      galoisFixedLogShell (K := K) (L := L) (p := p) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, integers_subset_integralLogShell (p := p) hx, rfl⟩

end

end LeanFormal.IUT.LocalFieldLogarithm
