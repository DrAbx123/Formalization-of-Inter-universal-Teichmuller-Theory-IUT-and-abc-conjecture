/- G1-A: smoothness of the infinity chart ring R2 n = Q[u,v]/(1+u^n-v^n) over Q.
   Strategy (avoids localization identifications): for D(u) and D(v) separately,
   compose the naive pre-submersive presentation of R2 (1 relation G, jacobian n u^(n-1) resp -n v^(n-1))
   with the canonical submersive localization presentation at u (resp. v);
   in the localization the composed jacobian is (n u^(n-1)) * u = n u^n (unit), giving rel dim 1.
   Cover {u, v} spans top, so chartRing2_locally_standardSmooth follows, hence the scheme-level result.
   No sorry/admit/axiom/PUnit/True/toy. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmooth2Actual
open Polynomial MvPolynomial
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual

/-- R2 n 的两个坐标类。 -/
noncomputable def u2 (n : Nat) : R2 n :=
  Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 0)

noncomputable def v2 (n : Nat) : R2 n :=
  Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 1)

/-- R2 中的关系 1 + u^n = v^n。 -/
theorem one_add_u2_pow (n : Nat) : 1 + u2 n ^ n - v2 n ^ n = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {secondEquation n}) (secondEquation n) : R2 n) = 0 :=
    secondRelation_eq_zero n
  change (1 + Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 0) ^ n
    - Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 1) ^ n : R2 n) = 0
  have h2 : (Ideal.Quotient.mk (Ideal.span {secondEquation n}) (secondEquation n) : R2 n)
      = 1 + Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 0) ^ n
        - Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.X 1) ^ n := by
    rw [secondEquation]
    simp only [map_sub, map_add, map_pow, map_one]
  rw [h2] at h
  exact h

/-- n 在 R2 n 中可逆。 -/
theorem natCast_isUnit2 (n : Nat) (hn : 0 < n) : IsUnit (n : R2 n) := by
  have hnq : IsUnit ((n : Rat)) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  have h := hnq.map (algebraMap Rat (R2 n))
  simpa using h

/-- u、v 生成单位理想。 -/
theorem u2_v2_span_eq_top (n : Nat) (hn : 0 < n) :
    Ideal.span ({u2 n, v2 n} : Set (R2 n)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem : (1 : R2 n) ∈ Ideal.span ({u2 n, v2 n} : Set (R2 n)) := by
    have hrel := one_add_u2_pow n
    have hup : u2 n * u2 n ^ (n - 1) = u2 n ^ n := by
      rw [← pow_succ', show n - 1 + 1 = n from by omega]
    have hvp : v2 n * v2 n ^ (n - 1) = v2 n ^ n := by
      rw [← pow_succ', show n - 1 + 1 = n from by omega]
    have h1 : (1 : R2 n) = v2 n * v2 n ^ (n - 1) - u2 n * u2 n ^ (n - 1) := by
      rw [hup, hvp]
      linear_combination hrel
    rw [h1]
    refine Ideal.sub_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  exact hmem

#print axioms one_add_u2_pow
#print axioms u2_v2_span_eq_top
/-- G 对 X0 的偏导：n X0^(n-1)。 -/
theorem pderiv_secondEquation_zero (n : Nat) :
    MvPolynomial.pderiv (0 : Fin 2) (secondEquation n)
      = (n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 0 ^ (n - 1) := by
  rw [secondEquation]
  simp only [map_add, map_sub, map_one, MvPolynomial.pderiv_X, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_one, mul_zero, sub_zero, add_zero]
  ring

/-- G 对 X1 的偏导：- n X1^(n-1)。 -/
theorem pderiv_secondEquation_one (n : Nat) :
    MvPolynomial.pderiv (1 : Fin 2) (secondEquation n)
      = -((n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 1 ^ (n - 1)) := by
  rw [secondEquation]
  simp only [map_add, map_sub, map_one, MvPolynomial.pderiv_X,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), Pi.single_eq_same,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_one, mul_zero, sub_zero, add_zero]
  ring

/-- 商的理想一致：span(range 常函数 G) = span{G}。 -/
theorem span_range_secondEquation (n : Nat) :
    Ideal.span (Set.range (fun _ : Fin 1 => secondEquation n))
      = Ideal.span ({secondEquation n} : Set (MvPolynomial (Fin 2) ℚ)) := by
  congr 1
  ext x
  constructor
  · rintro ⟨_, rfl⟩
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩

/-- 该商与 R2 n 的 ℚ-代数同构。 -/
noncomputable def qEq (n : Nat) :
    (MvPolynomial (Fin 2) ℚ ⧸ Ideal.span (Set.range (fun _ : Fin 1 => secondEquation n)))
      ≃ₐ[ℚ] R2 n :=
  Ideal.quotientEquivAlgOfEq ℚ (span_range_secondEquation n)

/-- 单关系 naive pre-submersive presentation（R2 的 G，map 选变量 i，再经 qEq 到 R2）。 -/
noncomputable def preR2 (n : Nat) (i : Fin 2) :
    Algebra.PreSubmersivePresentation ℚ (R2 n) (Fin 2) (Fin 1) :=
  (Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 => secondEquation n)
    (fun _ => i) (fun a b _ => Subsingleton.elim a b)).ofAlgEquiv (qEq n)

/-- naive presentation 的 jacobian = algebraMap (pderiv i G)。 -/
theorem naive_jacobian (n : Nat) (i : Fin 2) :
    (Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 => secondEquation n)
      (fun _ => i) (fun a b _ => Subsingleton.elim a b)).jacobian
      = algebraMap (MvPolynomial (Fin 2) ℚ)
          (MvPolynomial (Fin 2) ℚ ⧸ Ideal.span (Set.range (fun _ : Fin 1 => secondEquation n)))
          (MvPolynomial.pderiv i (secondEquation n)) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  congr 1
  rw [Matrix.det_fin_one]
  exact Algebra.PreSubmersivePresentation.jacobiMatrix_naive _ _ _ _ 0 0

/-- preR2 的 jacobian = algebraMap (pderiv i G)。 -/
theorem preR2_jacobian (n : Nat) (i : Fin 2) :
    (preR2 n i).jacobian
      = algebraMap (MvPolynomial (Fin 2) ℚ) (R2 n)
          (MvPolynomial.pderiv i (secondEquation n)) := by
  rw [preR2, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv, naive_jacobian]
  rw [Ideal.Quotient.algebraMap_eq, qEq, Ideal.quotientEquivAlgOfEq_mk]
  rw [Ideal.Quotient.algebraMap_eq]

#print axioms span_range_secondEquation
#print axioms preR2_jacobian
/-- 局部化中 n 可逆。 -/
theorem natCast_isUnit_localized (n : Nat) (hn : 0 < n) (f : R2 n) :
    IsUnit (n : Localization.Away f) := by
  have hnq : IsUnit ((n : Rat)) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  have h := hnq.map (algebraMap Rat (Localization.Away f))
  simpa using h

/-- 两重 algebraMap：algebraMap_M_T = algebraMap (R2) T ∘ algebraMap M (R2)。 -/
theorem algebraMap_comp_apply (n : Nat) (x : MvPolynomial (Fin 2) ℚ) :
    (algebraMap (R2 n) (Localization.Away (u2 n)))
      ((algebraMap (MvPolynomial (Fin 2) ℚ) (R2 n)) x)
      = algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (u2 n)) x := by
  rw [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq (MvPolynomial (Fin 2) ℚ) (R2 n)
    (Localization.Away (u2 n))]

/-- algebraMap M T X0 = algebraMap (R2) T u2（点式，不 rewrite u2 以免破坏实例）。 -/
theorem algebraMap_X0_eq (n : Nat) :
    algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (u2 n)) (MvPolynomial.X 0)
      = algebraMap (R2 n) (Localization.Away (u2 n)) (u2 n) := by
  rw [← algebraMap_comp_apply n (MvPolynomial.X 0)]
  congr 1

/-- **D(u) 上 (R2)[1/u] 是 rel dim 1 standard smooth**（presentation 组合：P_0 ∘ loc(u)）。 -/
theorem loc_u2_standardSmooth (n : Nat) (hn : 0 < n) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away (u2 n)) := by
  let Qpre : Algebra.PreSubmersivePresentation (R2 n) (Localization.Away (u2 n)) Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway (Localization.Away (u2 n)) (u2 n)
  let compPre : Algebra.PreSubmersivePresentation ℚ (Localization.Away (u2 n))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
    Qpre.comp (preR2 n 0)
  have hdim0 : Qpre.dimension = 0 := by
    simp [Algebra.Presentation.dimension]
  have hdimP : (preR2 n 0).dimension = 1 := by
    simp [Algebra.Presentation.dimension]
  have hdim : compPre.dimension = 1 := by
    have h := Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
      (Q := Qpre) (P := preR2 n 0)
    rw [show compPre.dimension = Qpre.dimension + (preR2 n 0).dimension from h]
    rw [hdim0, hdimP, zero_add]
  have hjac : IsUnit compPre.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def]
    have hPjac : algebraMap (R2 n) (Localization.Away (u2 n)) ((preR2 n 0).jacobian)
        = algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (u2 n))
            (MvPolynomial.pderiv 0 (secondEquation n)) := by
      rw [preR2_jacobian, algebraMap_comp_apply]
    rw [hPjac, pderiv_secondEquation_zero, map_mul, map_pow, map_natCast]
    have hQ : Qpre.jacobian = algebraMap (R2 n) (Localization.Away (u2 n)) (u2 n) :=
      Algebra.PreSubmersivePresentation.localizationAway_jacobian
        (S := Localization.Away (u2 n)) (u2 n)
    rw [hQ]
    have hU : IsUnit (algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (u2 n))
        (MvPolynomial.X 0)) := by
      rw [algebraMap_X0_eq n]
      exact IsLocalization.Away.algebraMap_isUnit (u2 n)
    have hnT : IsUnit ((n : Localization.Away (u2 n))) := natCast_isUnit_localized n hn (u2 n)
    refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit (u2 n))
    exact IsUnit.mul hnT (hU.pow (n - 1))
  let P : Algebra.SubmersivePresentation ℚ (Localization.Away (u2 n))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
    { toPreSubmersivePresentation := compPre, jacobian_isUnit := hjac }
  exact Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension P hdim

#print axioms algebraMap_comp_apply
#print axioms algebraMap_X0_eq
#print axioms loc_u2_standardSmooth
/-- 两重 algebraMap（v-侧）。 -/
theorem algebraMap_comp_apply_v (n : Nat) (x : MvPolynomial (Fin 2) ℚ) :
    (algebraMap (R2 n) (Localization.Away (v2 n)))
      ((algebraMap (MvPolynomial (Fin 2) ℚ) (R2 n)) x)
      = algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (v2 n)) x := by
  rw [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq (MvPolynomial (Fin 2) ℚ) (R2 n)
    (Localization.Away (v2 n))]

theorem algebraMap_X1_eq (n : Nat) :
    algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (v2 n)) (MvPolynomial.X 1)
      = algebraMap (R2 n) (Localization.Away (v2 n)) (v2 n) := by
  rw [← algebraMap_comp_apply_v n (MvPolynomial.X 1)]
  congr 1

/-- **D(v) 上 (R2)[1/v] 是 rel dim 1 standard smooth**（presentation 组合：P_1 ∘ loc(v)）。 -/
theorem loc_v2_standardSmooth (n : Nat) (hn : 0 < n) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away (v2 n)) := by
  let Qpre : Algebra.PreSubmersivePresentation (R2 n) (Localization.Away (v2 n)) Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway (Localization.Away (v2 n)) (v2 n)
  let compPre : Algebra.PreSubmersivePresentation ℚ (Localization.Away (v2 n))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
    Qpre.comp (preR2 n 1)
  have hdim0 : Qpre.dimension = 0 := by
    simp [Algebra.Presentation.dimension]
  have hdimP : (preR2 n 1).dimension = 1 := by
    simp [Algebra.Presentation.dimension]
  have hdim : compPre.dimension = 1 := by
    have h := Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
      (Q := Qpre) (P := preR2 n 1)
    rw [show compPre.dimension = Qpre.dimension + (preR2 n 1).dimension from h]
    rw [hdim0, hdimP, zero_add]
  have hjac : IsUnit compPre.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def]
    have hPjac : algebraMap (R2 n) (Localization.Away (v2 n)) ((preR2 n 1).jacobian)
        = algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (v2 n))
            (MvPolynomial.pderiv 1 (secondEquation n)) := by
      rw [preR2_jacobian, algebraMap_comp_apply_v]
    rw [hPjac, pderiv_secondEquation_one, map_neg, map_mul, map_pow, map_natCast]
    have hQ : Qpre.jacobian = algebraMap (R2 n) (Localization.Away (v2 n)) (v2 n) :=
      Algebra.PreSubmersivePresentation.localizationAway_jacobian
        (S := Localization.Away (v2 n)) (v2 n)
    rw [hQ]
    have hV : IsUnit (algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (v2 n))
        (MvPolynomial.X 1)) := by
      rw [algebraMap_X1_eq n]
      exact IsLocalization.Away.algebraMap_isUnit (v2 n)
    have hnT : IsUnit ((n : Localization.Away (v2 n))) := natCast_isUnit_localized n hn (v2 n)
    have hprod : IsUnit (-((n : Localization.Away (v2 n))
        * (algebraMap (MvPolynomial (Fin 2) ℚ) (Localization.Away (v2 n))
            (MvPolynomial.X 1)) ^ (n - 1)) * algebraMap (R2 n)
            (Localization.Away (v2 n)) (v2 n)) := by
      refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit (v2 n))
      exact (IsUnit.mul hnT (hV.pow (n - 1))).neg
    exact hprod
  let P : Algebra.SubmersivePresentation ℚ (Localization.Away (v2 n))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
    { toPreSubmersivePresentation := compPre, jacobian_isUnit := hjac }
  exact Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension P hdim

#print axioms loc_v2_standardSmooth
/-- **algebraMap ℚ (R2 n) 局部 standard smooth rel dim 1**：u、v 覆盖（理想=⊤），
    两局部化都是 rel dim 1 standard smooth。 -/
theorem chartRing2_locally_standardSmooth (n : Nat) (hn : 0 < n) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (R2 n)) := by
  refine ⟨{u2 n, v2 n}, u2_v2_span_eq_top n hn, ?_⟩
  intro t ht
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · rw [← IsScalarTower.algebraMap_eq ℚ (R2 n) (Localization.Away (u2 n))]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
      (loc_u2_standardSmooth n hn)
  · rw [← IsScalarTower.algebraMap_eq ℚ (R2 n) (Localization.Away (v2 n))]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
      (loc_v2_standardSmooth n hn)

/-- **∞-chart 的 affine 结构态射 `Spec (R2 n) ⟶ Spec ℚ` 是 rel dim 1 smooth**（scheme 层）。 -/
theorem chartSpec2_smoothOfRelativeDimension (n : Nat) (hn : 0 < n) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (R2 n)))) := by
  exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.SmoothOfRelativeDimension 1)
    (φ := CommRingCat.ofHom (algebraMap ℚ (R2 n)))).mpr
    (chartRing2_locally_standardSmooth n hn)

#print axioms chartRing2_locally_standardSmooth
#print axioms chartSpec2_smoothOfRelativeDimension



end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmooth2Actual