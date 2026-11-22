/- G1-A: R n is smooth over Q (relative dimension 1), via the localization-span criterion.
   Cover: ideal (chartR, chartR2) = top in Chart n (since n is a unit and
   chartX * chartR + chartY * chartR2 = n * (chartX^n + chartY^n) = n).
   Both localizations (R n)[1/r] and (R n)[1/r2] are standard smooth of rel dim 1
   (Mzk1G1FermatChartLocalizeSwapActual), hence Smooth; then RingHom.Smooth.ofLocalizationSpanTarget.
   No sorry/admit/axiom/PUnit/True/toy. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartLocalizeSwapActual
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothActual
open Polynomial MvPolynomial
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothLocalizeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSwapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartLocalizeSwapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothAttemptActual

/-- n is a unit in the Q-algebra Chart n. -/
theorem natCast_isUnit (n : Nat) (hn : 0 < n) : IsUnit (n : Chart n) := by
  have hnq : IsUnit ((n : Rat)) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  have h := hnq.map (algebraMap Rat (Chart n))
  simpa using h

/-- chartX * chartR = n * chartX^n. -/
theorem chartX_mul_chartR (n : Nat) (hn : 0 < n) :
    chartX n * chartR n = (n : Chart n) * chartX n ^ n := by
  rw [chartR, ← mul_assoc, mul_comm (chartX n) (n : Chart n), mul_assoc]
  rw [← pow_succ', show n - 1 + 1 = n from by omega]

/-- chartY * chartR2 = n * chartY^n. -/
theorem chartY_mul_chartR2 (n : Nat) (hn : 0 < n) :
    chartY n * chartR2 n = (n : Chart n) * chartY n ^ n := by
  rw [chartR2, ← mul_assoc, mul_comm (chartY n) (n : Chart n), mul_assoc]
  rw [← pow_succ', show n - 1 + 1 = n from by omega]

/-- chartX * chartR + chartY * chartR2 = n. -/
theorem chartX_chartR_add (n : Nat) (hn : 0 < n) :
    chartX n * chartR n + chartY n * chartR2 n = (n : Chart n) := by
  rw [chartX_mul_chartR n hn, chartY_mul_chartR2 n hn]
  have h := chart_relation n
  linear_combination (n : Chart n) * h

/-- The two specializations r = n x^(n-1) and r2 = n y^(n-1) generate the unit ideal. -/
theorem chartR_span_eq_top (n : Nat) (hn : 0 < n) :
    Ideal.span ({chartR n, chartR2 n} : Set (Chart n)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem : (n : Chart n) ∈ Ideal.span ({chartR n, chartR2 n} : Set (Chart n)) := by
    rw [← chartX_chartR_add n hn]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  obtain ⟨u, hu⟩ := natCast_isUnit n hn
  rw [← Units.inv_mul u]
  exact Ideal.mul_mem_left _ _ (by rwa [hu])

#print axioms chartX_chartR_add
#print axioms chartR_span_eq_top
/-- 局部化是 Smooth：standard smooth（rel dim 1）→ Smooth（经 ring hom 版本）。 -/
theorem loc_isSmooth (n : Nat) (r : Chart n)
    (hstd : Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away r)) :
    Algebra.Smooth ℚ (Localization.Away r) := by
  rw [← RingHom.smooth_algebraMap]
  haveI hstd' : Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away r) := hstd
  haveI : Algebra.IsStandardSmooth ℚ (Localization.Away r) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  exact RingHom.IsStandardSmooth.smooth
    ((RingHom.isStandardSmooth_algebraMap).mpr ‹Algebra.IsStandardSmooth ℚ (Localization.Away r)›)

/-- **R n 在 ℚ 上 smooth（相对维数 1）**：由 r、r2 的局部化覆盖（理想 = ⊤）与两个局部化的
    standard smooth 经 `RingHom.Smooth.ofLocalizationSpanTarget` 拼出。 -/
theorem chartRing_smooth (n : Nat) (hn : 0 < n) : Algebra.Smooth ℚ (Chart n) := by
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.Smooth.ofLocalizationSpanTarget (f := algebraMap ℚ (Chart n))
    ({chartR n, chartR2 n} : Set (Chart n)) (chartR_span_eq_top n hn) ?_
  rintro ⟨r, hr⟩
  have hr' : r = chartR n ∨ r = chartR2 n := by simpa using hr
  change ((algebraMap (Chart n) (Localization.Away r)).comp (algebraMap ℚ (Chart n))).Smooth
  rcases hr' with h | h
  · rw [h, ← IsScalarTower.algebraMap_eq ℚ (Chart n) (Localization.Away (chartR n))]
    exact (RingHom.smooth_algebraMap).mpr (loc_isSmooth n (chartR n) (loc_chartR_isStandardSmooth n))
  · rw [h, ← IsScalarTower.algebraMap_eq ℚ (Chart n) (Localization.Away (chartR2 n))]
    exact (RingHom.smooth_algebraMap).mpr (loc_isSmooth n (chartR2 n) (loc_chartR2_isStandardSmooth n))

#print axioms loc_isSmooth
#print axioms chartRing_smooth
/-- 每一点处存在 basic open 使 (Chart n)[1/f] 是 rel dim 1 standard smooth：
    p 不含 r 时取 f = r；否则 p 不含 r2（否则 1 ∈ p），取 f = r2。 -/
theorem chartRing_exists_standardSmooth_localized (n : Nat) (hn : 0 < n)
    (p : Ideal (Chart n)) [p.IsPrime] :
    ∃ f : Chart n, f ∉ p ∧ Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away f) := by
  have hnot : ¬ (chartR n ∈ p ∧ chartR2 n ∈ p) := by
    rintro ⟨h1, h2⟩
    have hle : Ideal.span ({chartR n, chartR2 n} : Set (Chart n)) ≤ p :=
      Ideal.span_le.mpr (by
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact h1
        · exact h2)
    have htop : Ideal.span ({chartR n, chartR2 n} : Set (Chart n)) = ⊤ := chartR_span_eq_top n hn
    have hone : (1 : Chart n) ∈ p := hle (by rw [htop]; exact Submodule.mem_top)
    have hptop : p = ⊤ := eq_top_iff.mpr (by
      intro x _
      have hx : x * (1 : Chart n) ∈ p := Ideal.mul_mem_left p x hone
      simpa using hx)
    exact ‹p.IsPrime›.ne_top hptop
  by_cases h : chartR n ∈ p
  · exact ⟨chartR2 n, fun h2 => hnot ⟨h, h2⟩, loc_chartR2_isStandardSmooth n⟩
  · exact ⟨chartR n, h, loc_chartR_isStandardSmooth n⟩

#print axioms chartRing_exists_standardSmooth_localized
/-- **algebraMap ℚ (Chart n) 局部 standard smooth rel dim 1**：r、r2 覆盖（理想=⊤），
    两局部化都是 rel dim 1 standard smooth。这是 scheme 层 SmoothOfRelativeDimension 1 的
    `RingHom.Locally` 输入。 -/
theorem chartRing_locally_standardSmooth (n : Nat) (hn : 0 < n) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (Chart n)) := by
  refine ⟨{chartR n, chartR2 n}, chartR_span_eq_top n hn, ?_⟩
  intro t ht
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · rw [← IsScalarTower.algebraMap_eq ℚ (Chart n) (Localization.Away (chartR n))]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
      (loc_chartR_isStandardSmooth n)
  · rw [← IsScalarTower.algebraMap_eq ℚ (Chart n) (Localization.Away (chartR2 n))]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
      (loc_chartR2_isStandardSmooth n)

#print axioms chartRing_locally_standardSmooth
/-- **λ-chart 的 affine 结构态射 `Spec (Chart n) ⟶ Spec ℚ` 是 rel dim 1 smooth**（scheme 层）：
    经 `HasRingHomProperty.Spec_iff` 化归 ring hom 的 `Locally (IsStandardSmoothOfRelativeDimension 1)`，
    后者由 chartR/chartR2 覆盖 + 两局部化 standard smooth 给出。 -/
theorem chartSpec_smoothOfRelativeDimension (n : Nat) (hn : 0 < n) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Chart n)))) := by
  exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.SmoothOfRelativeDimension 1)
    (φ := CommRingCat.ofHom (algebraMap ℚ (Chart n)))).mpr
    (chartRing_locally_standardSmooth n hn)

#print axioms chartSpec_smoothOfRelativeDimension





end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothActual