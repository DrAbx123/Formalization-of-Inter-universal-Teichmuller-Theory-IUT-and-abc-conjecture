import tmp.sheaf.xif.paper.S1015FractionalLatticeOpenActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegerTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
/-! # S1022: local fractional lattice spans the local field over Qp
F(a) contains p^k O_hol for an integer k >= a, and p^k is a unit scalar.
Since span O = top, span F(a) = top. -/
noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000
namespace LeanFormal.IUT.XiFPaper.S1022LocalFracSpanTopActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.FinitePadicIntegralLattice
universe u
theorem span_padicFractionalLattice_eq_top
    (p : Nat) [Fact p.Prime]
    (K : Type u) [NormedField K] [IsUltrametricDist K]
    [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (a : Real) :
    Submodule.span ℚ_[p] (padicFractionalLattice (p := p) (K := K) a : Set K) = ⊤ := by
  obtain ⟨k, hk⟩ := exists_int_gt a
  have hk' : a ≤ (k : Real) := le_of_lt hk
  let rq : ℚ_[p] := (p : ℚ_[p]) ^ k
  let rK : K := (p : K) ^ k
  have hrq_ne : rq ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hrK_eq : rK = algebraMap ℚ_[p] K rq := by
    simp [rK, rq, map_zpow₀, map_natCast]
  have hr_norm : ‖rK‖ = (p : Real) ^ (-(k : Real)) := by
    simpa [rK] using norm_prime_zpow (p := p) (K := K) k
  have hscaled : (fun x : K => rq • x) '' (valuationIntegerLattice (K := K) (p := p) : Set K) ⊆
      (padicFractionalLattice (p := p) (K := K) a : Set K) := by
    rintro y ⟨x, hx, rfl⟩
    change ‖rq • x‖ ≤ (p : Real) ^ (-a)
    have hxnorm : ‖x‖ ≤ 1 := (mem_integers_iff x).mp hx
    have hry : ‖rq • x‖ = ‖rK‖ * ‖x‖ := by
      rw [Algebra.smul_def, hrK_eq, norm_mul]
    rw [hry, hr_norm]
    calc
      (p : Real) ^ (-(k : Real)) * ‖x‖ ≤ (p : Real) ^ (-(k : Real)) * 1 :=
        mul_le_mul_of_nonneg_left hxnorm (Real.rpow_nonneg (by positivity) _)
      _ ≤ (p : Real) ^ (-a) := by
        rw [mul_one]
        exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le)
          (by linarith : -(k : Real) ≤ -a)
  have hspan_scaled : Submodule.span ℚ_[p]
      ((fun x : K => rq • x) '' (valuationIntegerLattice (K := K) (p := p) : Set K)) = ⊤ := by
    rw [show (fun x : K => rq • x) '' (valuationIntegerLattice (K := K) (p := p) : Set K) =
        rq • (valuationIntegerLattice (K := K) (p := p) : Set K) by rfl]
    rw [Submodule.span_smul_eq_of_isUnit _ rq (isUnit_iff_ne_zero.mpr hrq_ne)]
    exact span_padic_valuationIntegerLattice_eq_top (p := p) (K := K)
  apply top_unique
  rw [← hspan_scaled]
  exact Submodule.span_mono hscaled
end LeanFormal.IUT.XiFPaper.S1022LocalFracSpanTopActual
