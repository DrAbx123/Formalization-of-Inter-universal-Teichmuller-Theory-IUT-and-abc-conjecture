import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Actual trace-dual volume block (route two)

This file starts the actual-Haar trace-dual block requested by task-75.
It imports the existing integral trace-dual lattice API and the actual
finite-dimensional Qp Haar p-scaling theorem.

Delivered here: (B3) double dual for a basis integral lattice, and the
scalar (B4)/(B5) relative Haar-volume block for a scalar p-power dilation.
The general-lattice B4 remains a listed gap in ROUTE2-TOOL-INVENTORY.md.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TraceDualVolumeActual

open MeasureTheory
open LeanFormal.IUT.IntegralTraceDual
open LeanFormal.IUT.FinitePadicIntegralLattice
open LeanFormal.IUT.FinitePadicHaarScaling
open scoped Pointwise ENNReal

noncomputable section

universe u

variable {p : Nat} [Fact p.Prime]
variable {M : Type u} [NormedAddCommGroup M] [NormedSpace ℚ_[p] M]
  [FiniteDimensional ℚ_[p] M] [MeasurableSpace M] [BorelSpace M]

/-- Double dual of a basis integral lattice under a nondegenerate symmetric
bilinear form is the original lattice. -/
theorem doubleDual_basisIntegralLattice
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    {i : Type*} [Fintype i] [DecidableEq i]
    (b : Module.Basis i ℚ_[p] M) :
    padicIntegralTraceDualLattice B
        (padicIntegralTraceDualLattice B (basisIntegralLattice b)) =
      basisIntegralLattice b := by
  rw [padicIntegralTraceDualLattice_span_basis B hB b]
  change padicIntegralTraceDualLattice B (basisIntegralLattice (B.dualBasis hB b)) =
    basisIntegralLattice b
  rw [padicIntegralTraceDualLattice_span_basis B hB (B.dualBasis hB b)]
  rw [LinearMap.BilinForm.dualBasis_dualBasis hB hBsymm b]
  rfl

/-- Scalar multiplication as a ℤ_[p]-linear endomorphism. -/
def smulLinearMap (a : ℚ_[p]) : M →ₗ[ℤ_[p]] M where
  toFun x := a • x
  map_add' x y := by simp [smul_add]
  map_smul' r x := by
    change a • ((r : ℚ_[p]) • x) = (r : ℚ_[p]) • (a • x)
    rw [smul_comm]

/-- Scalar dilation of a ℤ_[p]-submodule. -/
def smulSubmodule (a : ℚ_[p]) (O : Submodule ℤ_[p] M) : Submodule ℤ_[p] M :=
  O.map (smulLinearMap (p := p) a)

@[simp] theorem smulLinearMap_apply (a : ℚ_[p]) (x : M) :
    smulLinearMap (p := p) a x = a • x := rfl

theorem mem_smulSubmodule_iff {a : ℚ_[p]} {O : Submodule ℤ_[p] M} {x : M} :
    x ∈ smulSubmodule (p := p) a O ↔ ∃ y ∈ O, a • y = x := by
  rw [smulSubmodule, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h⟩

/-- The integral trace dual of a scalar dilation is the inverse scalar
dilation of the integral trace dual. -/
theorem traceDual_smulSubmodule
    (B : LinearMap.BilinForm ℚ_[p] M) (a : ℚ_[p]) (ha : a ≠ 0)
    (O : Submodule ℤ_[p] M) :
    padicIntegralTraceDualLattice B (smulSubmodule (p := p) a O) =
      smulSubmodule (p := p) a⁻¹ (padicIntegralTraceDualLattice B O) := by
  ext x
  constructor
  · intro hx
    rw [mem_smulSubmodule_iff]
    refine ⟨a • x, ?_, ?_⟩
    · rw [mem_padicIntegralTraceDualLattice_iff] at hx ⊢
      intro y hy
      have h := hx (a • y) (by
        rw [mem_smulSubmodule_iff]
        exact ⟨y, hy, rfl⟩)
      rw [LinearMap.map_smul] at h ⊢
      exact h
    · rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  · intro hx
    rw [mem_smulSubmodule_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [mem_padicIntegralTraceDualLattice_iff] at hz ⊢
    intro y hy
    rw [mem_smulSubmodule_iff] at hy
    rcases hy with ⟨w, hw, rfl⟩
    have h := hz w hw
    rw [B.smul_left, B.smul_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    exact h

/-- Positive p-power Haar scaling in a finite-dimensional ℚ_[p] space. -/
theorem measure_pow_smul_finiteDimensional
    (mu : Measure M) [Measure.IsAddHaarMeasure mu] (k : Nat) (S : Set M) :
    mu (((p : ℚ_[p]) ^ k) • S) =
      ((p : ENNReal) ^ (k * Module.finrank ℚ_[p] M))⁻¹ * mu S := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      rw [← smul_smul]
      rw [measure_prime_smul_finiteDimensional]
      rw [ih]
      rw [Nat.succ_mul]
      rw [← mul_assoc]
      rw [ENNReal.inv_pow, ENNReal.inv_pow, ← pow_add]
      rw [Nat.add_comm]
      rw [ENNReal.inv_pow]

/-- Inverse p-power Haar scaling. -/
theorem measure_inv_pow_smul_finiteDimensional
    (mu : Measure M) [Measure.IsAddHaarMeasure mu] (k : Nat) (S : Set M) :
    mu ((((p : ℚ_[p]) ^ k)⁻¹) • S) =
      ((p : ENNReal) ^ (k * Module.finrank ℚ_[p] M)) * mu S := by
  let c : ENNReal := (p : ENNReal) ^ (k * Module.finrank ℚ_[p] M)
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hctop : c ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have h := measure_pow_smul_finiteDimensional (p := p) (M := M) mu k
    ((((p : ℚ_[p]) ^ k)⁻¹) • S)
  rw [smul_smul] at h
  rw [mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)), one_smul] at h
  rw [h]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]

@[simp] theorem coe_smulSubmodule (a : ℚ_[p]) (O : Submodule ℤ_[p] M) :
    (smulSubmodule (p := p) a O : Set M) = a • (O : Set M) := by
  ext x
  constructor
  · intro hx
    change x ∈ smulSubmodule (p := p) a O at hx
    rw [smulSubmodule, Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, h⟩
    exact ⟨y, hy, h⟩
  · intro hx
    rw [Set.mem_smul_set] at hx
    rcases hx with ⟨y, hy, h⟩
    change x ∈ Submodule.map (smulLinearMap (p := p) a) O
    rw [Submodule.mem_map]
    exact ⟨y, hy, h⟩

/-- Scalar (B4) relative Haar-volume identity: for a scalar p-power dilation
of any Z_p-lattice O, the relative volume of L and its trace dual is the
reciprocal relative volume of O and O#.  This is the actual-Haar product form
of mu(L)/mu(O) * mu(L#)/mu(O#) = 1. -/
theorem relativeHaarVolume_scalar_traceDual
    (B : LinearMap.BilinForm ℚ_[p] M) (O : Submodule ℤ_[p] M)
    (mu : Measure M) [Measure.IsAddHaarMeasure mu] (k : Nat) :
    mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O) *
        mu (padicIntegralTraceDualLattice B
          (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O)) =
      mu (O : Set M) *
        mu (padicIntegralTraceDualLattice B O : Set M) := by
  let c : ENNReal := (p : ENNReal) ^ (k * Module.finrank ℚ_[p] M)
  have ha : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hctop : c ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  rw [traceDual_smulSubmodule B ((p : ℚ_[p]) ^ k) ha O]
  have h1 : mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O) = c⁻¹ * mu (O : Set M) := by
    rw [coe_smulSubmodule, measure_pow_smul_finiteDimensional]
  have h2 : mu (smulSubmodule (p := p) (((p : ℚ_[p]) ^ k)⁻¹)
        (padicIntegralTraceDualLattice B O)) =
      c * mu (padicIntegralTraceDualLattice B O : Set M) := by
    rw [coe_smulSubmodule, measure_inv_pow_smul_finiteDimensional]
  rw [h1, h2]
  calc
    c⁻¹ * mu (O : Set M) * (c * mu (padicIntegralTraceDualLattice B O : Set M))
        = c⁻¹ * (c * (mu (O : Set M) * mu (padicIntegralTraceDualLattice B O : Set M))) := by
          ac_rfl
    _ = mu (O : Set M) * mu (padicIntegralTraceDualLattice B O : Set M) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-- Log form of the scalar (B5) identity. -/
theorem relativeHaarLog_scalar_traceDual
    (B : LinearMap.BilinForm ℚ_[p] M) (O : Submodule ℤ_[p] M)
    (mu : Measure M) [Measure.IsAddHaarMeasure mu] (k : Nat)
    (hLpos : 0 < mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O : Set M))
    (hLfin : mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O : Set M) < ⊤)
    (hOpos : 0 < mu (O : Set M)) (hOfin : mu (O : Set M) < ⊤)
    (hDpos : 0 < mu (padicIntegralTraceDualLattice B
      (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O) : Set M))
    (hDfin : mu (padicIntegralTraceDualLattice B
      (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O) : Set M) < ⊤)
    (hOsharpPos : 0 < mu (padicIntegralTraceDualLattice B O : Set M))
    (hOsharpFin : mu (padicIntegralTraceDualLattice B O : Set M) < ⊤) :
    Real.log (mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O : Set M)).toReal -
        Real.log (mu (O : Set M)).toReal =
      - (Real.log (mu (padicIntegralTraceDualLattice B
            (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O) : Set M)).toReal -
          Real.log (mu (padicIntegralTraceDualLattice B O : Set M)).toReal) := by
  have hprod := relativeHaarVolume_scalar_traceDual (p := p) (M := M) B O mu k
  have hmul : (mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O) *
        mu (padicIntegralTraceDualLattice B
          (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O))).toReal =
      (mu (O : Set M) * mu (padicIntegralTraceDualLattice B O : Set M)).toReal := by
    rw [hprod]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hmul
  have hlog := congrArg Real.log hmul
  have hx0 : (mu (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O)).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos hLpos.ne' hLfin.ne).ne'
  have hy0 : (mu (padicIntegralTraceDualLattice B
        (smulSubmodule (p := p) ((p : ℚ_[p]) ^ k) O))).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos hDpos.ne' hDfin.ne).ne'
  have ho0 : (mu (O : Set M)).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hd0 : (mu (padicIntegralTraceDualLattice B O : Set M)).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos hOsharpPos.ne' hOsharpFin.ne).ne'
  rw [Real.log_mul hx0 hy0, Real.log_mul ho0 hd0] at hlog
  linarith

end

end LeanFormal.IUT.XiFPaper.Mzk1TraceDualVolumeActual

-- watchdog recompile marker: source updated for queue pickup.
