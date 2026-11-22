/- G1-A §2.3：∞-chart 上 π 的有限性。R2 n = ℚ[X0,X1]/(1 + X0^n − X1^n) 作为 ℚ[t]-代数
   （t ↦ z1^n = 1 + z0^n）是有限模。与 λ-chart 文件对称：
   z1 整（z1^n = t）、z0 整（z0^n = t − 1），adjoin=⊤，故 Algebra.IsIntegral+FiniteType ⟹ Module.Finite，
   再 → RingHom.Finite → IsFinite.SpecMap_iff。不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual
open Polynomial MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open AlgebraicGeometry CategoryTheory

/-- ∞-chart 图环 R2 n。 -/
abbrev R2 (n : Nat) : Type := Mzk1G1FermatSecondChartActual.R2 n

noncomputable def z0 (n : Nat) : R2 n :=
  Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 0)

noncomputable def z1 (n : Nat) : R2 n :=
  Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 1)

/-- t ↦ z1^n 的环同态（∞-chart 的 t-chart map）。 -/
noncomputable def lamHom2 (n : Nat) : Polynomial ℚ →+* R2 n :=
  (Polynomial.aeval (z1 n ^ n)).toRingHom

noncomputable instance lamAlgebra2 (n : Nat) : Algebra (Polynomial ℚ) (R2 n) :=
  (lamHom2 n).toAlgebra

theorem algebraMap_eq_lamHom2 (n : Nat) :
    (algebraMap (Polynomial ℚ) (R2 n)) = lamHom2 n := rfl

theorem lamHom2_X (n : Nat) : (lamHom2 n) Polynomial.X = z1 n ^ n := by
  rw [lamHom2]
  exact Polynomial.aeval_X (z1 n ^ n)

theorem algebraMap_C_eq2 (n : Nat) (r : ℚ) :
    (algebraMap (Polynomial ℚ) (R2 n)) (Polynomial.C r) = algebraMap ℚ (R2 n) r := by
  rw [algebraMap_eq_lamHom2, lamHom2]
  simp

/-- R2 n 中的关系 `1 + z0^n = z1^n`。 -/
theorem one_add_z0_pow_eq_z1_pow (n : Nat) : 1 + z0 n ^ n - z1 n ^ n = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {secondEquation n}) (secondEquation n) : R2 n) = 0 :=
    secondRelation_eq_zero n
  have key : (Ideal.Quotient.mk (Ideal.span {secondEquation n}) (secondEquation n) : R2 n)
      = 1 + Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 0 ^ n)
        - Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 1 ^ n) := by
    rw [secondEquation]
    simp only [map_sub, map_add, map_pow, map_one]
  rw [z0, z1, ← map_pow, ← map_pow, ← key]
  exact h

theorem mk_C_eq_algebraMap2 (n : Nat) (r : ℚ) :
    (Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.C r) : R2 n)
      = algebraMap ℚ (R2 n) r := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 2) ℚ) (R2 n)]
  rw [Ideal.Quotient.algebraMap_eq]
  rw [show (algebraMap ℚ (MvPolynomial (Fin 2) ℚ) r) = MvPolynomial.C r from rfl]

/-- z1 整：monic `X^n - t`。 -/
theorem z1_isIntegral (n : Nat) (hn : 0 < n) : IsIntegral (Polynomial ℚ) (z1 n) := by
  refine ⟨Polynomial.X ^ n - Polynomial.C Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn)
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [algebraMap_eq_lamHom2, lamHom2_X, sub_self]

/-- z0 整：monic `X^n - (t - 1)`。 -/
theorem z0_isIntegral (n : Nat) (hn : 0 < n) : IsIntegral (Polynomial ℚ) (z0 n) := by
  refine ⟨Polynomial.X ^ n - Polynomial.C (Polynomial.X - 1), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    calc (Polynomial.C (Polynomial.X - 1) : Polynomial (Polynomial ℚ)).degree ≤ 0 :=
        Polynomial.degree_C_le
      _ < n := by exact_mod_cast hn
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [algebraMap_eq_lamHom2, map_sub, map_one, lamHom2_X]
    have h := one_add_z0_pow_eq_z1_pow n
    linear_combination h

theorem adjoin_eq_top2 (n : Nat) :
    Algebra.adjoin (Polynomial ℚ) ({z0 n, z1 n} : Set (R2 n)) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {secondEquation n}) a
  have key : ∀ p : MvPolynomial (Fin 2) ℚ,
      Ideal.Quotient.mk (Ideal.span {secondEquation n}) p
        ∈ Algebra.adjoin (Polynomial ℚ) ({z0 n, z1 n} : Set (R2 n)) := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun q => Ideal.Quotient.mk (Ideal.span {secondEquation n}) q
        ∈ Algebra.adjoin (Polynomial ℚ) ({z0 n, z1 n} : Set (R2 n))) p ?_ ?_ ?_
    · intro r
      rw [mk_C_eq_algebraMap2, ← algebraMap_C_eq2 n r]
      exact Subalgebra.algebraMap_mem _ _
    · intro p q hp hq
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    · intro p i hp
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      fin_cases i
      · exact Algebra.subset_adjoin (by simp [z0])
      · exact Algebra.subset_adjoin (by simp [z1])
  exact key p

noncomputable instance chart_finiteType2 (n : Nat) :
    Algebra.FiniteType (Polynomial ℚ) (R2 n) := by
  classical
  refine ⟨?fg⟩
  rw [Subalgebra.fg_def]
  exact ⟨({z0 n, z1 n} : Set (R2 n)), Set.toFinite _, adjoin_eq_top2 n⟩

theorem chart_isIntegral2 (n : Nat) (hn : 0 < n) :
    Algebra.IsIntegral (Polynomial ℚ) (R2 n) where
  isIntegral x := by
    have hmem : x ∈ Algebra.adjoin (Polynomial ℚ) ({z0 n, z1 n} : Set (R2 n)) := by
      rw [adjoin_eq_top2 n]; trivial
    exact Algebra.adjoin_induction (p := fun y _ => IsIntegral (Polynomial ℚ) y)
      (fun y hy => by
        rcases hy with rfl | rfl
        · exact z0_isIntegral n hn
        · exact z1_isIntegral n hn)
      (fun r => isIntegral_algebraMap)
      (fun y z _ _ hy hz => hy.add hz)
      (fun y z _ _ hy hz => hy.mul hz) hmem

/-- **R2 n 在 ℚ[t]（t ↦ z1^n = 1 + z0^n）上有限**：∞-chart 版 IsFinite π 核心。 -/
theorem chartRing_finite2 (n : Nat) (hn : 0 < n) : Module.Finite (Polynomial ℚ) (R2 n) :=
  haveI := chart_isIntegral2 n hn
  Algebra.IsIntegral.finite (R := Polynomial ℚ) (A := R2 n) (h' := chart_finiteType2 n)

theorem lamHom2_finite (n : Nat) (hn : 0 < n) : (lamHom2 n).Finite := by
  show Module.Finite (Polynomial ℚ) (R2 n)
  exact chartRing_finite2 n hn

/-- ∞-chart 上 π 的有限性：`Spec (R2 n) → Spec ℚ[t]`。 -/
theorem lamHom2Spec_isFinite (n : Nat) (hn : 0 < n) :
    IsFinite (Spec.map (CommRingCat.ofHom (lamHom2 n))) := by
  rw [IsFinite.SpecMap_iff]
  exact lamHom2_finite n hn

#print axioms one_add_z0_pow_eq_z1_pow
#print axioms z0_isIntegral
#print axioms z1_isIntegral
#print axioms adjoin_eq_top2
#print axioms chartRing_finite2
#print axioms lamHom2Spec_isFinite

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual