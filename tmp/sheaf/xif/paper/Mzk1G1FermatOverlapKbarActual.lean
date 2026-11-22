/- G1-A route 2.4 L144 (h): the kbar-base-changed overlap ring is a domain.
   Reuse check: Overlap0 n = Localization.Away (x0 n) (FermatOverlapActual:92);
   Mathlib IsLocalization.isDomain_of_le_nonZeroDivisors (Localization/Defs.lean:889) +
   IsLocalization.tensorProduct_tensorProduct (Localization/BaseChange.lean:363) +
   Algebra.TensorProduct.lift (TensorProduct/Maps.lean:155). Conclusion: ADAPTER (no new math).
   Reuses our route-new chartKbar_isDomain (18:11:22). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1ChartKbarActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial MvPolynomial
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapKbarActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothGeomIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual

abbrev K : Type := FermatK
abbrev Poly2 : Type := MvPolynomial (Fin 2) ℚ

/-- 点 (1,0) 处的赋值：X0 ↦ 1, X1 ↦ 0。 -/
noncomputable def eval01 (n : Nat) : Poly2 →ₐ[ℚ] K :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (1 : K) else 0)

theorem eval01_fermatEquation (n : Nat) (hn : 0 < n) : eval01 n (fermatEquation n) = 0 := by
  rw [fermatEquation_def]
  simp [eval01, hn.ne']

#print axioms eval01_fermatEquation
/-- Chart0Ring n →ₐ[ℚ] k̄：过商后在 (1,0) 处赋值。 -/
noncomputable def chart0_eval01 (n : Nat) (hn : 0 < n) : Chart0Ring n →ₐ[ℚ] K :=
  Ideal.Quotient.liftₐ (ideal0 n) (eval01 n) (by
    rw [ideal0_def]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr (eval01_fermatEquation n hn))))

theorem chart0_eval01_x0 (n : Nat) (hn : 0 < n) : chart0_eval01 n hn (x0 n) = 1 := by
  simp [chart0_eval01, x0, eval01]

/-- Chart0Ring n ⊗[ℚ] k̄ →ₐ[ℚ] k̄（在 (1,0) 处赋值，k̄-线性延拓）。 -/
noncomputable def evK (n : Nat) (hn : 0 < n) : Chart0Ring n ⊗[ℚ] K →ₐ[ℚ] K :=
  Algebra.TensorProduct.lift (chart0_eval01 n hn) (AlgHom.id ℚ K)
    (fun _ _ => Commute.all _ _)

/-- 一阶张量 `x0 ⊗ 1`（在 Chart0⊗k̄ 中）非零：用 (1,0) 赋值。 -/
theorem tmulOne_ne_zero (n : Nat) (hn : 0 < n) :
    ((x0 n) ⊗ₜ[ℚ] (1 : K) : Chart0Ring n ⊗[ℚ] K) ≠ 0 := by
  intro h
  have h1 : evK n hn ((x0 n) ⊗ₜ[ℚ] (1 : K)) = 1 := by
    simp [evK, Algebra.TensorProduct.lift_tmul, chart0_eval01_x0 n hn]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- 一阶张量 `1 ⊗ x0`（在 k̄⊗Chart0 中）非零：镜像 (1,0) 赋值。 -/
theorem one_tmul_ne_zero (n : Nat) (hn : 0 < n) :
    ((1 : K) ⊗ₜ[ℚ] (x0 n) : K ⊗[ℚ] Chart0Ring n) ≠ 0 := by
  intro h
  let evK' : K ⊗[ℚ] Chart0Ring n →ₐ[ℚ] K :=
    Algebra.TensorProduct.lift (AlgHom.id ℚ K) (chart0_eval01 n hn)
      (fun _ _ => Commute.all _ _)
  have h1 : evK' ((1 : K) ⊗ₜ[ℚ] (x0 n)) = 1 := by
    simp [evK', Algebra.TensorProduct.lift_tmul, chart0_eval01_x0 n hn]
  rw [h] at h1
  have h1' : evK' (0 : K ⊗[ℚ] Chart0Ring n) = 1 := h1
  rw [map_zero] at h1'
  exact zero_ne_one h1'

#print axioms tmulOne_ne_zero
#print axioms one_tmul_ne_zero


/-- **overlap ⊗ k̄ 是整环**（route §2.4 L144 重叠整性部分）。 -/
theorem overlapKbar_isDomain (n : Nat) (hn : 0 < n) :
    IsDomain (Overlap0 n ⊗[ℚ] K) := by
  haveI hDom : IsDomain (Chart0Ring n ⊗[ℚ] K) :=
    Mzk1G1ChartKbarActual.chartKbar_isDomain n hn
  haveI hDomK : IsDomain (K ⊗[ℚ] Chart0Ring n) :=
    (Algebra.TensorProduct.comm (R := ℚ) (A := Chart0Ring n) (B := K)).toRingEquiv.isDomain_iff.mp
      hDom
  letI hNZ : NoZeroDivisors (K ⊗[ℚ] Chart0Ring n) :=
    IsDomain.to_noZeroDivisors (K ⊗[ℚ] Chart0Ring n)
  let e1 : Overlap0 n ⊗[ℚ] K ≃ₐ[ℚ] K ⊗[ℚ] Overlap0 n :=
    Algebra.TensorProduct.comm (R := ℚ) (A := Overlap0 n) (B := K)
  let e2 : K ⊗[ℚ] Overlap0 n ≃ₐ[ℚ] Localization.Away ((1 : K) ⊗ₜ[ℚ] (x0 n)) :=
    (IsLocalization.Away.tensorProductEquivTMulRight (R := ℚ) (S := K)
      (A := Chart0Ring n) (x0 n) (Overlap0 n)).restrictScalars ℚ
  haveI hLocal : IsDomain (Localization.Away ((1 : K) ⊗ₜ[ℚ] (x0 n))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (S := Localization.Away ((1 : K) ⊗ₜ[ℚ] (x0 n)))
      (M := Submonoid.powers ((1 : K) ⊗ₜ[ℚ] (x0 n))) (by
        intro m hm
        obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff m ((1 : K) ⊗ₜ[ℚ] (x0 n))).mp hm
        rw [← hk]
        have h0 : ((1 : K) ⊗ₜ[ℚ] (x0 n)) ≠ 0 := one_tmul_ne_zero n hn
        exact mem_nonZeroDivisors_of_ne_zero
          (pow_ne_zero (a := ((1 : K) ⊗ₜ[ℚ] (x0 n))) k h0))
  exact (e1.toRingEquiv.trans e2.toRingEquiv).isDomain_iff.mpr hLocal

#print axioms overlapKbar_isDomain

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapKbarActual