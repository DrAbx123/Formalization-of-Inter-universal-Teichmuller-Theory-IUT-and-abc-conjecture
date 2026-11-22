import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicExpLog
import LeanFormal.IUT.Foundations.LocalFields.PadicFreeDecomposition
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel

/-! # Log-shell saturation: parts (a),(c),(d). -/

noncomputable section

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.FinitePadicIntegralLattice
open scoped BigOperators Pointwise LeanFormal.IUT.FinitePadicIntegralLattice

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- Part (a). -/
theorem coe_integralLogShellLattice_eq :
    (integralLogShellLattice (K := K) (p := p) : Set K) =
      (integralLogShell (K := K) (p := p) : Set K) := rfl

/-- Part (a). -/
theorem mem_integralLogShellLattice_iff {x : K} :
    x ∈ integralLogShellLattice (K := K) (p := p) ↔
      x ∈ integralLogShell (K := K) (p := p) := Iff.rfl

/-- Part (c). -/
theorem coe_integralLogShell_eq_range :
    (integralLogShell (K := K) (p := p) : Set K) =
      Set.range (fun u : (Integers K)ˣ =>
        (logShellScale p : K)⁻¹ * unitLog (K := K) u) := rfl

/-- Part (d): p-adic decomposition of the actual integral log-shell. -/
theorem integralLogShell_padicDecomposition {y : K}
    (hy : y ∈ integralLogShell (K := K) (p := p)) (hne : y ≠ 0) :
    ∃ (n : ℕ) (z : integralLogShellLattice (K := K) (p := p)),
      y = (p : ℤ_[p]) ^ n • (z : K) ∧
        z ∉ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (integralLogShellLattice (K := K) (p := p))) := by
  let y' : integralLogShellLattice (K := K) (p := p) := ⟨y, hy⟩
  have hy' : y' ≠ 0 := by
    intro h
    exact hne (congrArg Subtype.val h)
  obtain ⟨n, z, hyz, hz⟩ :=
    exists_pow_smul_notMem_p_smul_top (p := p) (M := integralLogShellLattice (K := K) (p := p)) hy'
  refine ⟨n, z, ?_, hz⟩
  exact congrArg Subtype.val hyz

/-- Part (d), shell form: the primitive factor in the p-adic decomposition of a
nonzero integral log-shell element is not divisible by p inside the shell. -/
theorem integralLogShell_primitive_notMem_smul {y : K}
    (hy : y ∈ integralLogShell (K := K) (p := p)) (hne : y ≠ 0) :
    ∃ (n : ℕ) (z : K), z ∈ integralLogShell (K := K) (p := p) ∧
      y = (p : ℤ_[p]) ^ n • z ∧
      z ∉ (p : ℤ_[p]) • (integralLogShell (K := K) (p := p) : Set K) := by
  obtain ⟨n, zl, hyz, hzprim⟩ :=
    integralLogShell_padicDecomposition (K := K) (p := p) hy hne
  refine ⟨n, (zl : K), ?_⟩
  refine ⟨zl.2, hyz, ?_⟩
  intro hzshell
  obtain ⟨w, hw, hwz⟩ := Set.mem_smul_set.mp hzshell
  apply hzprim
  refine (Submodule.mem_smul_pointwise_iff_exists zl (p : ℤ_[p])
    (⊤ : Submodule ℤ_[p] (integralLogShellLattice (K := K) (p := p)))).mpr ⟨⟨w, hw⟩, ?_⟩
  refine ⟨Submodule.mem_top, ?_⟩
  apply Subtype.ext
  simpa using hwz


/-- Scalar normalization: a power of the p-adic integer p acts on K as
multiplication by the corresponding Nat power. -/
theorem padicInt_pow_smul_eq_natCast_pow_mul (n : ℕ) (w : K) :
    ((p : ℤ_[p]) ^ n) • w = ((((p : ℕ) ^ n : ℕ) : K) * w) := by
  rw [padicInteger_smul_eq (p := p)]
  push_cast
  rw [Algebra.smul_def]
  push_cast
  rfl

/-- Unit-level generation up to torsion: every integral unit is a p-power
iterate of a unit modulo the (torsion) kernel of the p-adic logarithm. -/
theorem integralLogShell_unitLog_generation (u : (Integers K)ˣ) :
    ∃ (n : ℕ) (v : (Integers K)ˣ),
      unitLog u = ((((p : ℕ) ^ n : ℕ) : K) * unitLog v) ∧
        IsOfFinOrder (u * (v ^ ((p : ℕ) ^ n))⁻¹) := by
  let y : K := (logShellScale p : K)⁻¹ * unitLog u
  have hy_mem : y ∈ integralLogShell (K := K) (p := p) := ⟨u, rfl⟩
  have hscale_ne : (logShellScale p : K) ≠ 0 := by
    exact_mod_cast (ne_of_gt (logShellScale_pos (p := p)))
  have hscale : (logShellScale p : K) * y = unitLog u := by
    dsimp only [y]
    rw [← mul_assoc, mul_inv_cancel₀ hscale_ne, one_mul]
  by_cases hzero : y = 0
  · have hlog : unitLog u = 0 := by rw [← hscale, hzero, mul_zero]
    refine ⟨0, 1, ?_, ?_⟩
    · simp [hlog, unitLog_one (p := p)]
    · have hu : IsOfFinOrder u :=
        (unitLog_eq_zero_iff_isOfFinOrder (p := p) u).mp hlog
      simpa using hu
  · obtain ⟨n, z, hzmem, hyz, _⟩ :=
      integralLogShell_primitive_notMem_smul (K := K) (p := p) hy_mem hzero
    change ∃ v : (Integers K)ˣ, (logShellScale p : K)⁻¹ * unitLog v = z at hzmem
    obtain ⟨v, hv⟩ := hzmem
    have hgen : unitLog u = ((((p : ℕ) ^ n : ℕ) : K) * unitLog v) := by
      calc unitLog u = (logShellScale p : K) * y := hscale.symm
        _ = (logShellScale p : K) * (((p : ℤ_[p]) ^ n) • z) := by rw [hyz]
        _ = (logShellScale p : K) * (((((p : ℕ) ^ n : ℕ) : K)) * z) := by
              rw [padicInt_pow_smul_eq_natCast_pow_mul]
        _ = ((((p : ℕ) ^ n : ℕ) : K)) * ((logShellScale p : K) * z) := by ring
        _ = ((((p : ℕ) ^ n : ℕ) : K)) * unitLog v := by
              rw [show (logShellScale p : K) * z = unitLog v from by
                rw [← hv, ← mul_assoc, mul_inv_cancel₀ hscale_ne, one_mul]]
    refine ⟨n, v, hgen, ?_⟩
    have hlogv : unitLog (v ^ ((p : ℕ) ^ n)) =
        ((((p : ℕ) ^ n : ℕ) : K) * unitLog v) := by
      rw [unitLog_pow (p := p)]
    have hprod : unitLog (u * (v ^ ((p : ℕ) ^ n))⁻¹) = 0 := by
      rw [unitLog_mul (p := p), unitLog_inv (p := p), hlogv, hgen]
      ring
    exact (unitLog_eq_zero_iff_isOfFinOrder (p := p) _).mp hprod

end LeanFormal.IUT.LocalFieldLogarithm
end
