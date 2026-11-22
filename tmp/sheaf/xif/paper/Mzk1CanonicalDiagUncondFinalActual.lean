import tmp.sheaf.xif.paper.Mzk1CanonicalDiagReduceActual
import tmp.sheaf.xif.paper.Mzk1CanonicalDiagUncondActual
import tmp.sheaf.xif.paper.Mzk1CoordSmallBridgeActual
import tmp.sheaf.xif.paper.Mzk1CanonicalHaarCoordLatticeActual
import tmp.sheaf.xif.paper.S1015FractionalLatticeOpenActual
import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact

/-! B4 final: unconditional canonical diagonal volume ratio, without diagHomeo. -/
noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1CoordSmallBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagReduceActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondActual
open LeanFormal.IUT.XiFPaper.S1015FractionalLatticeOpenActual
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]

theorem mem_span_pow_iff (e : Nat) (x : ℚ_[p]) :
    x ∈ Submodule.span (PadicInt p) {((p : ℚ_[p]) ^ e)} ↔
      x ∈ (padicFractionalLattice (p := p) (K := ℚ_[p]) (e : ℝ) : Set ℚ_[p]) := by
  have hpnorm : ‖(p : ℚ_[p]) ^ e‖ = (p : ℝ) ^ (-(e : ℝ)) := by
    rw [Padic.norm_p_pow, ← Real.rpow_neg_natCast]
  have hpne : (p : ℚ_[p]) ^ e ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hfac : ((p : ℝ) ^ (-(e : ℝ))) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _).ne'
  constructor
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    change x ∈ padicFractionalLattice (p := p) (K := ℚ_[p]) (e : ℝ)
    rw [mem_padicFractionalLattice_iff]
    rw [← hc, Algebra.smul_def, norm_mul, hpnorm]
    exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one c)
  · intro hx
    change x ∈ padicFractionalLattice (p := p) (K := ℚ_[p]) (e : ℝ) at hx
    rw [mem_padicFractionalLattice_iff] at hx
    rw [Submodule.mem_span_singleton]
    let y : ℚ_[p] := ((p : ℚ_[p]) ^ e)⁻¹ * x
    have hy : ‖y‖ ≤ 1 := by
      calc
        ‖y‖ = ‖((p : ℚ_[p]) ^ e)⁻¹‖ * ‖x‖ := by
          rw [show y = ((p : ℚ_[p]) ^ e)⁻¹ * x from rfl, norm_mul]
        _ = ((p : ℝ) ^ (-(e : ℝ)))⁻¹ * ‖x‖ := by rw [norm_inv, hpnorm]
        _ ≤ ((p : ℝ) ^ (-(e : ℝ)))⁻¹ * ((p : ℝ) ^ (-(e : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hx (by positivity)
        _ = 1 := by
              exact inv_mul_cancel₀ hfac
    refine ⟨⟨y, ?_⟩, ?_⟩
    · exact (mem_integers_iff (K := ℚ_[p]) y).mpr hy
    · rw [Algebra.smul_def]
      change y * (p : ℚ_[p]) ^ e = x
      rw [show y = ((p : ℚ_[p]) ^ e)⁻¹ * x from rfl]
      field_simp [hpne]

theorem coordDual_eq_pi_fractional (f : d → Nat) :
    (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) =
      Set.pi Set.univ (fun i =>
        (padicFractionalLattice (p := p) (K := ℚ_[p]) (f i : ℝ) : Set ℚ_[p])) := by
  ext x
  change x ∈ (Submodule.pi Set.univ
      (fun i => Submodule.span (PadicInt p) {((p : ℚ_[p]) ^ (f i))}) :
        Submodule (PadicInt p) (d → ℚ_[p])) ↔
    x ∈ Set.pi Set.univ (fun i =>
      (padicFractionalLattice (p := p) (K := ℚ_[p]) (f i : ℝ) : Set ℚ_[p]))
  rw [Submodule.mem_pi]
  constructor
  · intro hx i _
    exact (mem_span_pow_iff (p := p) (f i) (x i)).mp (hx i (Set.mem_univ i))
  · intro hx i _
    exact (mem_span_pow_iff (p := p) (f i) (x i)).mpr (hx i (Set.mem_univ i))

theorem coordDual_le_coordSmall (f : d → Nat) :
    coordDual (p := p) (d := d) f ≤ coordSmall (p := p) (d := d) := by
  apply Submodule.pi_mono
  intro i _
  rw [Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  change ((p : ℚ_[p]) ^ (f i)) ∈
    Submodule.span (PadicInt p) ({(1 : ℚ_[p])} : Set ℚ_[p])
  rw [Submodule.mem_span_singleton]
  refine ⟨(p : PadicInt p) ^ f i, ?_⟩
  simp [Algebra.smul_def, map_pow]

theorem canonical_diag_volume_ratio_uncond (f : d → Nat) :
    (addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (coordDual (p := p) (d := d) f : Set (d → ℚ_[p]))).toReal /
      (addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (coordSmall (p := p) (d := d) : Set (d → ℚ_[p]))).toReal =
      (∏ i, (p : ℝ) ^ (f i))⁻¹ := by
  have hsmall : (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])) =
      padicIntegerCoordinateLattice (p := p) (ι := d) := by
    rw [coordSmall_eq_coordLattice, coordLattice_eq_padicIntegerCoordinateLattice]
  haveI : Finite d := Finite.of_fintype d
  have hLc : IsCompact (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])) := by
    rw [hsmall]; exact isCompact_padicIntegerCoordinateLattice
  have hLo : IsOpen (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])) := by
    rw [hsmall]; exact isOpen_padicIntegerCoordinateLattice
  have hXc : IsCompact (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) := by
    rw [coordDual_eq_pi_fractional]
    exact isCompact_univ_pi fun i =>
      isCompact_padicFractionalLattice_of_nonneg (p := p) (K := ℚ_[p])
        (f i : ℝ) (Nat.cast_nonneg _)
  have hXo : IsOpen (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) := by
    rw [coordDual_eq_pi_fractional]
    exact isOpen_set_pi Set.finite_univ (fun i _ =>
      isOpen_padicFractionalLattice p ℚ_[p] (f i : ℝ))
  exact canonical_diag_volume_ratio_compact_open (p := p) (d := d) f
    (coordDual_le_coordSmall f) hLc hLo hXc hXo

end LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondFinalActual
end