/- G1-A §2.3：λ-chart 上 π 的有限性。R n 作为 ℚ[λ]-代数（λ ↦ x^n）是有限模。
   路线：R n 由 x0,y1 生成（adjoin=⊤）、二者整（x0^n=λ、y1^n=1−λ 为 monic 关系），
   故 Algebra.IsIntegral + Algebra.FiniteType ⟹ Module.Finite（Mathlib 定理），
   再经 RingHom.Finite → IsFinite.SpecMap_iff 得 λ-chart 上 π 的 IsFinite。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual
open Polynomial MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open AlgebraicGeometry CategoryTheory

/-- 曲线图环 R n。 -/
abbrev R (n : Nat) : Type := Mzk1G1FermatAffineChartActual.R n

/-- x = X0 的类。 -/
noncomputable def x0 (n : Nat) : R n :=
  Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.X 0)

/-- y = X1 的类。 -/
noncomputable def y1 (n : Nat) : R n :=
  Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.X 1)

theorem x0_def (n : Nat) : x0 n
    = Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.X 0) := rfl

theorem y1_def (n : Nat) : y1 n
    = Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.X 1) := rfl

/-- λ ↦ x^n 的环同态（= henry 的 λ-chart map）。 -/
noncomputable def lamHom (n : Nat) : Polynomial ℚ →+* R n :=
  (Polynomial.aeval (x0 n ^ n)).toRingHom

/-- λ-chart 的代数结构。 -/
noncomputable instance lamAlgebra (n : Nat) : Algebra (Polynomial ℚ) (R n) :=
  (lamHom n).toAlgebra

theorem algebraMap_eq_lamHom (n : Nat) :
    (algebraMap (Polynomial ℚ) (R n)) = lamHom n := rfl

theorem lamHom_X (n : Nat) : (lamHom n) Polynomial.X = x0 n ^ n := by
  rw [lamHom]
  exact Polynomial.aeval_X (x0 n ^ n)

/-- R n 中的关系 `x^n + y^n = 1`。 -/
theorem algebraMap_C_eq (n : Nat) (r : ℚ) :
    (algebraMap (Polynomial ℚ) (R n)) (Polynomial.C r) = algebraMap ℚ (R n) r := by
  rw [algebraMap_eq_lamHom, lamHom]
  simp

theorem x0_pow_add_y1_pow (n : Nat) : x0 n ^ n + y1 n ^ n - 1 = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (fermatEquation n) : R n) = 0 :=
    fermatRelation_eq_zero n
  have key : (Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (fermatEquation n) : R n)
      = Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.X 0 ^ n)
        + Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.X 1 ^ n) - 1 := by
    rw [fermatEquation, map_sub, map_add, map_pow, map_pow, map_one]
  rw [x0, y1, ← map_pow, ← map_pow, ← key]
  exact h

/-- x0 整：monic `X^n - λ`。 -/
theorem x0_isIntegral (n : Nat) (hn : 0 < n) : IsIntegral (Polynomial ℚ) (x0 n) := by
  refine ⟨Polynomial.X ^ n - Polynomial.C Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn)
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [algebraMap_eq_lamHom, lamHom_X, sub_self]

/-- y1 整：monic `X^n - (1 - λ)`。 -/
theorem y1_isIntegral (n : Nat) (hn : 0 < n) : IsIntegral (Polynomial ℚ) (y1 n) := by
  refine ⟨Polynomial.X ^ n - Polynomial.C (1 - Polynomial.X), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    calc (Polynomial.C (1 - Polynomial.X) : Polynomial (Polynomial ℚ)).degree ≤ 0 :=
        Polynomial.degree_C_le
      _ < n := by exact_mod_cast hn
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [algebraMap_eq_lamHom, map_sub, map_one, lamHom_X]
    have h := x0_pow_add_y1_pow n
    linear_combination h

#print axioms x0_isIntegral
#print axioms y1_isIntegral
#print axioms x0_pow_add_y1_pow
/-! ### R n 由 x0,y1 生成 -/

theorem mk_C_eq_algebraMap (n : Nat) (r : ℚ) :
    (Ideal.Quotient.mk (Ideal.span {fermatEquation n}) (MvPolynomial.C r) : R n)
      = algebraMap ℚ (R n) r := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 2) ℚ) (R n)]
  rw [Ideal.Quotient.algebraMap_eq]
  rw [show (algebraMap ℚ (MvPolynomial (Fin 2) ℚ) r) = MvPolynomial.C r from rfl]

theorem adjoin_eq_top (n : Nat) :
    Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n)) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {fermatEquation n}) a
  have key : ∀ p : MvPolynomial (Fin 2) ℚ,
      Ideal.Quotient.mk (Ideal.span {fermatEquation n}) p
        ∈ Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n)) := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun q => Ideal.Quotient.mk (Ideal.span {fermatEquation n}) q
        ∈ Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n))) p ?_ ?_ ?_
    · intro r
      rw [mk_C_eq_algebraMap, ← algebraMap_C_eq n r]
      exact Subalgebra.algebraMap_mem _ _
    · intro p q hp hq
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    · intro p i hp
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      fin_cases i
      · exact Algebra.subset_adjoin (by simp [x0])
      · exact Algebra.subset_adjoin (by simp [y1])
  exact key p

noncomputable instance chart_finiteType (n : Nat) :
    Algebra.FiniteType (Polynomial ℚ) (R n) := by
  classical
  refine ⟨?fg⟩
  rw [Subalgebra.fg_def]
  exact ⟨({x0 n, y1 n} : Set (R n)), Set.toFinite _, adjoin_eq_top n⟩

theorem chart_isIntegral (n : Nat) (hn : 0 < n) :
    Algebra.IsIntegral (Polynomial ℚ) (R n) where
  isIntegral x := by
    have hmem : x ∈ Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n)) := by
      rw [adjoin_eq_top n]; trivial
    exact Algebra.adjoin_induction (p := fun y _ => IsIntegral (Polynomial ℚ) y)
      (fun y hy => by
        rcases hy with rfl | rfl
        · exact x0_isIntegral n hn
        · exact y1_isIntegral n hn)
      (fun r => isIntegral_algebraMap)
      (fun y z _ _ hy hz => hy.add hz)
      (fun y z _ _ hy hz => hy.mul hz) hmem

/-- **R n 在 ℚ[λ]（λ ↦ x^n）上有限**：IsFinite π 的 λ-chart 核心。 -/
theorem chartRing_finite (n : Nat) (hn : 0 < n) : Module.Finite (Polynomial ℚ) (R n) :=
  haveI := chart_isIntegral n hn
  Algebra.IsIntegral.finite (R := Polynomial ℚ) (A := R n) (h' := chart_finiteType n)

theorem lamHom_finite (n : Nat) (hn : 0 < n) : (lamHom n).Finite := by
  show Module.Finite (Polynomial ℚ) (R n)
  exact chartRing_finite n hn

/-- λ-chart 上 π 的有限性：`Spec (R n) → Spec ℚ[λ]`。 -/
theorem lamHomSpec_isFinite (n : Nat) (hn : 0 < n) :
    IsFinite (Spec.map (CommRingCat.ofHom (lamHom n))) := by
  rw [IsFinite.SpecMap_iff]
  exact lamHom_finite n hn

#print axioms mk_C_eq_algebraMap
#print axioms algebraMap_C_eq
#print axioms adjoin_eq_top
#print axioms chart_isIntegral
#print axioms chartRing_finite
#print axioms lamHom_finite
#print axioms lamHomSpec_isFinite

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual