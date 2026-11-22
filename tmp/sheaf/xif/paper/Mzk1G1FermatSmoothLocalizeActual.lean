/- G1-A §2.4 smooth 运输第一步：把局部化模型 `fermatModelRing` 接到真实图环 R n。
   目标：`fermatModelRing n` = ℚ[x,y,z]/(F, (n x^{n-1}) z - 1) 是 R n = ℚ[x,y]/(F)
   在 r = n x^{n-1} 处的局部化。本文件：
   * `chartToModel : R n →+* fermatModelRing n`（x,y ↦ x,y）及其实用引理；
   * 证明它把 r 送到单位；
   * 用 `IsLocalization.Away.lift` 得到 `localizeToModel : (R n)[1/r] →+* fermatModelRing n`。
   反向映射与互逆在下个文件。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothAttemptActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothIntegralActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothLocalizeActual
open Polynomial MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothAttemptActual

/-- 真实图环 R n。 -/
abbrev Chart (n : Nat) : Type :=
  LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveRing n

/-- 模型：ℚ[x,y,z]/(F, (n x^{n-1}) z - 1)。 -/
abbrev Model (n : Nat) : Type := fermatModelRing n

theorem chartIdeal_eq (n : Nat) :
    Chart n = (MvPolynomial (Fin 2) ℚ ⧸
      LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal n) := rfl

/-- 图坐标 x = X0 的类。 -/
noncomputable def chartX (n : Nat) : Chart n :=
  Ideal.Quotient.mk (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal n)
    (MvPolynomial.X 0)

/-- r = n * x^{n-1}：局部化点。 -/
noncomputable def chartR (n : Nat) : Chart n :=
  (n : Chart n) * chartX n ^ (n - 1)

theorem modelRel_zero_eq (n : Nat) :
    Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (fermatModelRel n 0) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self 0))

theorem modelRel_one_eq (n : Nat) :
    Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (fermatModelRel n 1) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self 1))

/-- 变量重命名 `Fin 2 → Fin 3`（x ↦ X0，y ↦ X1）。 -/
def fermatVarCast : Fin 2 → Fin 3 := Fin.castLE (by norm_num : 2 ≤ 3)

theorem rename_fermatCurvePoly (n : Nat) :
    MvPolynomial.rename fermatVarCast
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurvePoly n)
      = fermatModelRel n 0 := by
  rw [fermatModelRel_zero,
    LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurvePoly]
  simp [fermatVarCast]

/-- 图环到模型的环同态 `x ↦ x, y ↦ y`。 -/
noncomputable def chartToModel (n : Nat) : Chart n →+* Model n :=
  Ideal.Quotient.lift (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal n)
    ((Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))).comp
      (MvPolynomial.rename fermatVarCast).toRingHom) (by
      intro a ha
      rw [LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal,
        Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      have hF0 : ((Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))).comp
          (MvPolynomial.rename fermatVarCast).toRingHom)
          (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurvePoly n) = 0 := by
        rw [RingHom.comp_apply]
        change (Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))))
          (MvPolynomial.rename fermatVarCast
            (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurvePoly n)) = 0
        rw [rename_fermatCurvePoly, modelRel_zero_eq]
      rw [map_mul, hF0, zero_mul])

/-- `chartToModel` 在 x 上的值。 -/
theorem chartToModel_chartX (n : Nat) :
    chartToModel n (chartX n)
      = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X 0) := by
  rw [chartToModel, chartX, Ideal.Quotient.lift_mk]
  simp [fermatVarCast]

/-- `chartToModel` 在 r = n x^{n-1} 上的值是模型中的 `mk (n X0^{n-1})`。 -/
theorem chartToModel_chartR (n : Nat) :
    chartToModel n (chartR n)
      = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
          ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1)) := by
  rw [chartR, map_mul, map_pow, chartToModel_chartX]
  rw [show chartToModel n (n : Chart n) = (n : Model n) from map_natCast (chartToModel n) n]
  rw [map_mul, map_pow, map_natCast]

/-- r 在模型中的像是单位（关系 `(n x^{n-1}) z = 1`）。 -/
theorem chartToModel_chartR_isUnit (n : Nat) :
    IsUnit (chartToModel n (chartR n)) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1))) :=
    IsUnit.of_mul_eq_one _ (by
      have h := modelRel_one_eq n
      rw [fermatModelRel_one, map_sub, map_mul, map_one, sub_eq_zero] at h
      exact h)
  rwa [chartToModel_chartR]

/-- 局部化到模型的环同态 `(R n)[1/r] →+* fermatModelRing n`。 -/
noncomputable def localizeToModel (n : Nat) :
    Localization.Away (chartR n) →+* Model n :=
  IsLocalization.Away.lift (chartR n) (g := chartToModel n) (chartToModel_chartR_isUnit n)

#print axioms rename_fermatCurvePoly
#print axioms chartToModel_chartX
#print axioms chartToModel_chartR
#print axioms chartToModel_chartR_isUnit
#print axioms localizeToModel
/-! ### 反向映射 Model → (R n)[1/r] -/

/-- 图环中的 y = X1 类。 -/
noncomputable def chartY (n : Nat) : Chart n :=
  Ideal.Quotient.mk (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal n)
    (MvPolynomial.X 1)

/-- R n 中的关系 `x^n + y^n = 1`。 -/
theorem chart_relation (n : Nat) : chartX n ^ n + chartY n ^ n - 1 = 0 := by
  have h : Ideal.Quotient.mk
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal n)
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurvePoly n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurvePoly] at h
  simpa only [map_add, map_sub, map_pow, map_one, chartX, chartY] using h

/-- 模型变量在局部化中的赋值：X0 ↦ x, X1 ↦ y, X2 ↦ (n x^{n-1})^{-1}。 -/
noncomputable def modelAssign (n : Nat) : Fin 3 → Localization.Away (chartR n) :=
  Fin.cases (algebraMap (Chart n) (Localization.Away (chartR n)) (chartX n))
    (Fin.cases (algebraMap (Chart n) (Localization.Away (chartR n)) (chartY n))
      (fun _ => IsLocalization.Away.invSelf (chartR n)))

theorem modelAssign_zero (n : Nat) :
    modelAssign n 0 = algebraMap (Chart n) (Localization.Away (chartR n)) (chartX n) :=
  Fin.cases_zero ..

theorem modelAssign_one (n : Nat) :
    modelAssign n 1 = algebraMap (Chart n) (Localization.Away (chartR n)) (chartY n) := by
  show modelAssign n (Fin.succ (0 : Fin 2)) = _
  rw [modelAssign]
  rw [Fin.cases_succ]
  rfl

theorem modelAssign_two (n : Nat) :
    modelAssign n 2 = IsLocalization.Away.invSelf (chartR n) := by
  show modelAssign n (Fin.succ (Fin.succ (0 : Fin 1))) = _
  rw [modelAssign]
  rw [Fin.cases_succ, Fin.cases_succ]

/-- 模型的关系 `F = x^n + y^n - 1` 在局部化中的像为 0。 -/
theorem modelEval_rel_zero (n : Nat) :
    MvPolynomial.eval₂Hom (algebraMap ℚ (Localization.Away (chartR n))) (modelAssign n)
      (fermatModelRel n 0) = 0 := by
  rw [fermatModelRel_zero]
  have hcongr : algebraMap (Chart n) (Localization.Away (chartR n))
      (chartX n ^ n + chartY n ^ n - 1)
      = algebraMap (Chart n) (Localization.Away (chartR n)) (chartX n) ^ n
        + algebraMap (Chart n) (Localization.Away (chartR n)) (chartY n) ^ n - 1 := by
    rw [map_sub, map_add, map_pow, map_pow, map_one]
  rw [chart_relation n, map_zero] at hcongr
  simpa only [map_add, map_sub, map_pow, map_one, MvPolynomial.eval₂Hom_X',
    modelAssign_zero, modelAssign_one] using hcongr.symm

/-- 模型的关系 `(n x^{n-1}) z - 1` 在局部化中的像为 0。 -/
theorem modelEval_rel_one (n : Nat) :
    MvPolynomial.eval₂Hom (algebraMap ℚ (Localization.Away (chartR n))) (modelAssign n)
      (fermatModelRel n 1) = 0 := by
  rw [fermatModelRel_one]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, MvPolynomial.eval₂Hom_X',
    modelAssign_zero, modelAssign_two, map_natCast]
  -- goal: (n : Loc) * algebraMap x^(n-1) * invSelf - 1 = 0
  have hmul : algebraMap (Chart n) (Localization.Away (chartR n)) (chartR n)
      * IsLocalization.Away.invSelf (chartR n) = 1 :=
    IsLocalization.Away.mul_invSelf (chartR n)
  have hchartR : algebraMap (Chart n) (Localization.Away (chartR n)) (chartR n)
      = (n : Localization.Away (chartR n))
        * (algebraMap (Chart n) (Localization.Away (chartR n)) (chartX n)) ^ (n - 1) := by
    rw [chartR, map_mul, map_pow, map_natCast]
  rw [hchartR] at hmul
  rw [hmul, sub_self]

#print axioms chart_relation
#print axioms modelEval_rel_zero
#print axioms modelEval_rel_one
/-! ### Model → (R n)[1/r] 与互逆 -/

/-- 模型到局部化的环同态（X0 ↦ x, X1 ↦ y, X2 ↦ (n x^{n-1})^{-1}）。 -/
noncomputable def modelToLocalize (n : Nat) : Model n →+* Localization.Away (chartR n) :=
  Ideal.Quotient.lift (Ideal.span (Set.range (fermatModelRel n)))
    (MvPolynomial.eval₂Hom (algebraMap ℚ (Localization.Away (chartR n))) (modelAssign n)) (by
      intro a ha
      have hsubset : Set.range (fermatModelRel n) ⊆
          RingHom.ker (MvPolynomial.eval₂Hom (algebraMap ℚ (Localization.Away (chartR n)))
            (modelAssign n)) := by
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact modelEval_rel_zero n
        · exact modelEval_rel_one n
      have hmem : a ∈ RingHom.ker (MvPolynomial.eval₂Hom (algebraMap ℚ
          (Localization.Away (chartR n))) (modelAssign n)) := (Ideal.span_le.mpr hsubset) ha
      simpa using hmem)

theorem modelToLocalize_X0 (n : Nat) :
    modelToLocalize n (Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      (MvPolynomial.X 0)) = algebraMap (Chart n) (Localization.Away (chartR n)) (chartX n) := by
  rw [modelToLocalize, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
  rfl

theorem modelToLocalize_X1 (n : Nat) :
    modelToLocalize n (Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      (MvPolynomial.X 1)) = algebraMap (Chart n) (Localization.Away (chartR n)) (chartY n) := by
  rw [modelToLocalize, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
  exact modelAssign_one n

theorem modelToLocalize_X2 (n : Nat) :
    modelToLocalize n (Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      (MvPolynomial.X 2)) = IsLocalization.Away.invSelf (chartR n) := by
  rw [modelToLocalize, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
  exact modelAssign_two n

/-- `localizeToModel` 在 `algebraMap a` 上的值。 -/
theorem localizeToModel_algebraMap (n : Nat) (a : Chart n) :
    localizeToModel n (algebraMap (Chart n) (Localization.Away (chartR n)) a)
      = chartToModel n a :=
  IsLocalization.Away.lift_eq (chartR n) (chartToModel_chartR_isUnit n) a

/-- `localizeToModel` 在逆元上的值：等于模型中的 mk X2。 -/
theorem localizeToModel_invSelf (n : Nat) :
    localizeToModel n (IsLocalization.Away.invSelf (chartR n))
      = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X 2) := by
  set u : Model n := Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
    ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1)) with hu_def
  -- hx2 : mk X2 * u = 1
  have hx2 : Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X 2)
      * u = 1 := by
    have h := modelRel_one_eq n
    rw [fermatModelRel_one, map_sub, map_mul, map_one, sub_eq_zero] at h
    rw [← h]
    ring
  -- hu : localizeToModel(algebraMap r) = u
  have hu : localizeToModel n (algebraMap (Chart n) (Localization.Away (chartR n)) (chartR n))
      = u := by
    rw [localizeToModel_algebraMap, chartToModel_chartR]
  -- hinv : invSelfImage * u = 1
  have hinv : localizeToModel n (IsLocalization.Away.invSelf (chartR n)) * u = 1 := by
    rw [← hu, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have huunit : IsUnit u := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hx2)
  obtain ⟨U, hU⟩ : ∃ U : (Model n)ˣ, ↑U = u := ⟨huunit.unit, huunit.unit_spec⟩
  have key : ∀ a : Model n, a * u = 1 → a = ↑U⁻¹ := by
    intro a ha
    have haU : a * ↑U = 1 := by
      rw [hU]
      exact ha
    calc a = a * ↑U * ↑U⁻¹ := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = ↑U⁻¹ := by rw [haU, one_mul]
  rw [key _ hinv, key _ hx2]

#print axioms modelToLocalize_X0
#print axioms localizeToModel_invSelf
/-! ### 互逆之一：Model 端的复合是恒等 -/

/-- `chartToModel` 保留 ℚ-代数结构。 -/
theorem chartToModel_algebraMap (n : Nat) (q : ℚ) :
    chartToModel n (algebraMap ℚ (Chart n) q) = algebraMap ℚ (Model n) q := by
  change chartToModel n (Ideal.Quotient.mk
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual.fermatCurveIdeal n)
      (algebraMap ℚ (MvPolynomial (Fin 2) ℚ) q))
    = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      (algebraMap ℚ (MvPolynomial (Fin 3) ℚ) q)
  rw [chartToModel, Ideal.Quotient.lift_mk]
  simp [fermatVarCast]

/-- `chartToModel` 在 y 上的值。 -/
theorem chartToModel_chartY (n : Nat) :
    chartToModel n (chartY n)
      = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X 1) := by
  rw [chartToModel, chartY, Ideal.Quotient.lift_mk]
  simp [fermatVarCast]

/-- 复合 `localizeToModel ∘ modelToLocalize` 在模型上是恒等。 -/
theorem localizeToModel_modelToLocalize (n : Nat) :
    (localizeToModel n).comp (modelToLocalize n) = RingHom.id (Model n) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro q
    simp only [RingHom.comp_apply, RingHom.id_apply, MvPolynomial.eval₂Hom_C,
      Ideal.Quotient.lift_mk, map_mul]
    -- modelToLocalize (mk (C q)) = algebraMap q，再经 localizeToModel
    rw [modelToLocalize, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
    -- localizeToModel (algebraMap ℚ Loc q) = algebraMap ℚ Model q
    rw [IsScalarTower.algebraMap_apply ℚ (Chart n) (Localization.Away (chartR n))]
    rw [localizeToModel_algebraMap, chartToModel_algebraMap]
    rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 3) ℚ) (Model n)]
    simp
  · intro i
    fin_cases i
    · show (localizeToModel n) (modelToLocalize n (Ideal.Quotient.mk
          (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X (0 : Fin 3))))
        = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
          (MvPolynomial.X (0 : Fin 3))
      rw [modelToLocalize_X0, localizeToModel_algebraMap, chartToModel_chartX]
    · show (localizeToModel n) (modelToLocalize n (Ideal.Quotient.mk
          (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X (1 : Fin 3))))
        = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
          (MvPolynomial.X (1 : Fin 3))
      rw [modelToLocalize_X1, localizeToModel_algebraMap, chartToModel_chartY]
    · show (localizeToModel n) (modelToLocalize n (Ideal.Quotient.mk
          (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.X (2 : Fin 3))))
        = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
          (MvPolynomial.X (2 : Fin 3))
      rw [modelToLocalize_X2, localizeToModel_invSelf]

#print axioms chartToModel_algebraMap
#print axioms chartToModel_chartY
#print axioms localizeToModel_modelToLocalize
/-! ### Loc 端复合与 AlgEquiv -/

/-- `modelToLocalize` 保留 ℚ-代数结构。 -/
theorem modelToLocalize_algebraMap (n : Nat) (q : ℚ) :
    modelToLocalize n (algebraMap ℚ (Model n) q)
      = algebraMap ℚ (Localization.Away (chartR n)) q := by
  have harg : algebraMap ℚ (Model n) q
      = Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n))) (MvPolynomial.C q) := by
    rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 3) ℚ) (Model n)]
    simp only [MvPolynomial.algebraMap_eq]
    rw [Ideal.Quotient.algebraMap_eq]
  rw [harg, modelToLocalize, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]

/-- 复合 `modelToLocalize ∘ chartToModel` 等于局部化映射。 -/
theorem modelToLocalize_chartToModel (n : Nat) :
    (modelToLocalize n).comp (chartToModel n)
      = (algebraMap (Chart n) (Localization.Away (chartR n))) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro q
    show (modelToLocalize n) (chartToModel n (algebraMap ℚ (Chart n) q))
        = (algebraMap (Chart n) (Localization.Away (chartR n))) (algebraMap ℚ (Chart n) q)
    rw [chartToModel_algebraMap, modelToLocalize_algebraMap]
    rw [IsScalarTower.algebraMap_apply ℚ (Chart n) (Localization.Away (chartR n))]
  · intro i
    fin_cases i
    · show (modelToLocalize n) (chartToModel n (chartX n))
          = (algebraMap (Chart n) (Localization.Away (chartR n))) (chartX n)
      rw [chartToModel_chartX, modelToLocalize_X0]
    · show (modelToLocalize n) (chartToModel n (chartY n))
          = (algebraMap (Chart n) (Localization.Away (chartR n))) (chartY n)
      rw [chartToModel_chartY, modelToLocalize_X1]

/-- 复合 `modelToLocalize ∘ localizeToModel` 在局部化上是恒等。 -/
theorem modelToLocalize_localizeToModel (n : Nat) :
    (modelToLocalize n).comp (localizeToModel n)
      = RingHom.id (Localization.Away (chartR n)) := by
  have hgen := RingHom.congr_fun (modelToLocalize_chartToModel n)
  have hcomp_alg : ∀ a : Chart n,
      (modelToLocalize n) ((localizeToModel n)
        (algebraMap (Chart n) (Localization.Away (chartR n)) a))
        = algebraMap (Chart n) (Localization.Away (chartR n)) a := by
    intro a
    rw [localizeToModel_algebraMap]
    exact hgen a
  ext s
  have hk := IsLocalization.Away.sec_spec (chartR n) s
  -- 对 hk 两边取 modelToLocalize ∘ localizeToModel
  have h := congrArg (fun t => (modelToLocalize n) ((localizeToModel n) t)) hk
  have hA : (modelToLocalize n) ((localizeToModel n) s)
        * (algebraMap (Chart n) (Localization.Away (chartR n)))
          (chartR n ^ (IsLocalization.Away.sec (chartR n) s).2)
      = (algebraMap (Chart n) (Localization.Away (chartR n)))
          (IsLocalization.Away.sec (chartR n) s).1 := by
    simpa [map_mul, map_pow, hcomp_alg] using h
  have hcancel : IsUnit ((algebraMap (Chart n) (Localization.Away (chartR n)))
      (chartR n ^ (IsLocalization.Away.sec (chartR n) s).2)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (chartR n)).pow _
  obtain ⟨U, hU⟩ : ∃ U : (Localization.Away (chartR n))ˣ,
      ↑U = (algebraMap (Chart n) (Localization.Away (chartR n)))
        (chartR n ^ (IsLocalization.Away.sec (chartR n) s).2) :=
    ⟨hcancel.unit, hcancel.unit_spec⟩
  have hA' : (modelToLocalize n) ((localizeToModel n) s) * ↑U
      = (algebraMap (Chart n) (Localization.Away (chartR n)))
          (IsLocalization.Away.sec (chartR n) s).1 := by
    rw [hU]; exact hA
  have hk' : s * ↑U = (algebraMap (Chart n) (Localization.Away (chartR n)))
      (IsLocalization.Away.sec (chartR n) s).1 := by
    rw [hU]; exact hk
  calc (modelToLocalize n) ((localizeToModel n) s)
      = ((modelToLocalize n) ((localizeToModel n) s) * ↑U) * ↑U⁻¹ := by
          rw [mul_assoc, Units.mul_inv, mul_one]
    _ = ((algebraMap (Chart n) (Localization.Away (chartR n)))
          (IsLocalization.Away.sec (chartR n) s).1) * ↑U⁻¹ := by rw [hA']
    _ = (s * ↑U) * ↑U⁻¹ := by rw [hk']
    _ = s := by rw [mul_assoc, Units.mul_inv, mul_one]

/-- 局部化识别（route §2.4 smooth 运输关键）：
    `fermatModelRing n ≃ₐ[ℚ] (R n)[1/r]`，r = n x^{n-1}。 -/
noncomputable def localizeEquiv (n : Nat) :
    Model n ≃ₐ[ℚ] Localization.Away (chartR n) where
  toFun := modelToLocalize n
  invFun := localizeToModel n
  left_inv := fun m => by
    simpa using RingHom.congr_fun (localizeToModel_modelToLocalize n) m
  right_inv := fun s => by
    simpa using RingHom.congr_fun (modelToLocalize_localizeToModel n) s
  map_add' := map_add (modelToLocalize n)
  map_mul' := map_mul (modelToLocalize n)
  commutes' := fun q => modelToLocalize_algebraMap n q

#print axioms modelToLocalize_algebraMap
#print axioms modelToLocalize_chartToModel
#print axioms modelToLocalize_localizeToModel
#print axioms localizeEquiv

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothLocalizeActual