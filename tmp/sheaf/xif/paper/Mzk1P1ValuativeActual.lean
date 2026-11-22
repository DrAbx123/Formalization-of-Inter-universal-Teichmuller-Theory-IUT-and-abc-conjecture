/- P¹（两 chart 粘合模型）的 valuative criterion：存在性与唯一性。
   与 alan 的 Mzk1P1ProperActual（p1GluedToBase、QC/LFT/QS instances）配合，
   组装 IsProper p1GluedToBase。本文件只写 ValuativeCriterion 部分。 -/
import tmp.sheaf.xif.paper.Mzk1P1ProperActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

/-! ## 拓扑基础 -/

/-- Spec K（K 域）的像集是单点集。 -/
theorem range_eq_singleton_specField {K : Type} [Field K] {X : Scheme}
    (g : Spec (CommRingCat.of K) ⟶ X) : Set.range g.base = {g.base default} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨default, rfl⟩, ?_⟩
  rintro y ⟨z, rfl⟩
  rw [Unique.eq_default z]

/-- 闭点落在开浸入像中 ⇒ 整个像落在开浸入像中
（增值环 Spec R 的点都特殊化到闭点；开集对 generization 封闭）。 -/
theorem range_subset_of_closedPoint_mem {X Y : Scheme}
    {R : Type} [CommRing R] [IsDomain R] [ValuationRing R]
    (l : Spec (CommRingCat.of R) ⟶ X) (i : Y ⟶ X) [IsOpenImmersion i]
    (h : l.base (IsLocalRing.closedPoint R) ∈ Set.range i.base) :
    Set.range l.base ⊆ Set.range i.base := by
  rintro _ ⟨z, rfl⟩
  have hz : z ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint z
  have hsp : l.base z ⤳ l.base (IsLocalRing.closedPoint R) := hz.map l.continuous
  have hmem : l.base z ∈ i.opensRange := hsp.mem_open i.opensRange.2 h
  exact hmem

/-- 仿射比较：Spec R → Spec A 的两个态射若在分式域 K 上相同，则相等（R ⊂ K 单射）。 -/
theorem specMap_eq_of_comp_eq {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra R K] [IsFractionRing R K]
    {A : Type} [CommRing A]
    {u v : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A)}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ u =
         Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ v) :
    u = v := by
  have hpre := congrArg Spec.preimage h
  simp only [Spec.preimage_comp, Spec.preimage_map] at hpre
  have hfun : (Spec.preimage u).hom = (Spec.preimage v).hom := by
    refine RingHom.ext fun a => IsFractionRing.injective R K ?_
    have hcongr := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of K => f.hom a) hpre
    simpa using hcongr
  have hpre_eq : Spec.preimage u = Spec.preimage v := by
    apply CommRingCat.hom_ext
    exact hfun
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, hpre_eq]


/-! ## 归一化的 chart 态射刻画 -/

open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual

/-- 若 K-点 i₁ 经由 λ-chart 分解为 g，且 g 的坐标环同态在常数上是 ℚ-代数的，
则 i₁ 就是 chartMorphism0（坐标 = g 的 λ 值）。 -/
theorem eq_chartMorphism0_of_lift {K : Type} [Field K] [Algebra ℚ K]
    {i₁ : Spec (CommRingCat.of K) ⟶ projectiveLineGlued}
    (g : Spec (CommRingCat.of K) ⟶ chart0Scheme) (hg : g ≫ localChart0 = i₁)
    (hC : ∀ a : ℚ, (Spec.preimage g).hom (Polynomial.C a) = algebraMap ℚ K a) :
    i₁ = chartMorphism0 ((Spec.preimage g).hom Polynomial.X) := by
  have hhom : (Spec.preimage g).hom = evalAt ((Spec.preimage g).hom Polynomial.X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) (by rw [evalAt_X])
    rw [evalAt_C]
    exact hC a
  set lam : K := (Spec.preimage g).hom Polynomial.X with hlam
  have hg' : g = Spec.map (CommRingCat.ofHom (evalAt lam)) := by
    rw [← Spec.map_preimage g]
    congr 1
    apply CommRingCat.hom_ext
    simpa [hlam] using hhom
  calc i₁ = g ≫ localChart0 := hg.symm
    _ = Spec.map (CommRingCat.ofHom (evalAt lam)) ≫ localChart0 := by rw [hg']
    _ = chartMorphism0 lam := rfl

/-- t-chart 的对应刻画。 -/
theorem eq_chartMorphismInf_of_lift {K : Type} [Field K] [Algebra ℚ K]
    {i₁ : Spec (CommRingCat.of K) ⟶ projectiveLineGlued}
    (g : Spec (CommRingCat.of K) ⟶ chartInfScheme) (hg : g ≫ localChartInf = i₁)
    (hC : ∀ a : ℚ, (Spec.preimage g).hom (Polynomial.C a) = algebraMap ℚ K a) :
    i₁ = chartMorphismInf ((Spec.preimage g).hom Polynomial.X) := by
  have hhom : (Spec.preimage g).hom = evalAt ((Spec.preimage g).hom Polynomial.X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) (by rw [evalAt_X])
    rw [evalAt_C]
    exact hC a
  set lam : K := (Spec.preimage g).hom Polynomial.X with hlam
  have hg' : g = Spec.map (CommRingCat.ofHom (evalAt lam)) := by
    rw [← Spec.map_preimage g]
    congr 1
    apply CommRingCat.hom_ext
    simpa [hlam] using hhom
  calc i₁ = g ≫ localChartInf := hg.symm
    _ = Spec.map (CommRingCat.ofHom (evalAt lam)) ≫ localChartInf := by rw [hg']
    _ = chartMorphismInf lam := rfl


/-! ## chart 态射的自然性与基本成员关系 -/

/-- 基变换 R → K 下 λ-chart 态射的自然性。 -/
theorem specMap_comp_chartMorphism0 {R K : Type} [CommRing R] [Algebra ℚ R] [Field K]
    [Algebra R K] [Algebra ℚ K] [IsScalarTower ℚ R K] (r : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ chartMorphism0 r =
      chartMorphism0 (algebraMap R K r) := by
  have hring : (algebraMap R K).comp (evalAt r) = evalAt (algebraMap R K r) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, evalAt_C, evalAt_C]
      exact (IsScalarTower.algebraMap_apply ℚ R K a).symm
    · rw [RingHom.comp_apply, evalAt_X, evalAt_X]
  show Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      (Spec.map (CommRingCat.ofHom (evalAt r)) ≫ localChart0) =
    Spec.map (CommRingCat.ofHom (evalAt (algebraMap R K r))) ≫ localChart0
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

/-- 基变换 R → K 下 t-chart 态射的自然性。 -/
theorem specMap_comp_chartMorphismInf {R K : Type} [CommRing R] [Algebra ℚ R] [Field K]
    [Algebra R K] [Algebra ℚ K] [IsScalarTower ℚ R K] (r : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ chartMorphismInf r =
      chartMorphismInf (algebraMap R K r) := by
  have hring : (algebraMap R K).comp (evalAt r) = evalAt (algebraMap R K r) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, evalAt_C, evalAt_C]
      exact (IsScalarTower.algebraMap_apply ℚ R K a).symm
    · rw [RingHom.comp_apply, evalAt_X, evalAt_X]
  show Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      (Spec.map (CommRingCat.ofHom (evalAt r)) ≫ localChartInf) =
    Spec.map (CommRingCat.ofHom (evalAt (algebraMap R K r))) ≫ localChartInf
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

/-- chartMorphism0 的像落在 λ-chart 内。 -/
theorem chartMorphism0_mem_chart0 {R : Type} [CommRing R] [Algebra ℚ R] (r : R)
    (y : Spec (CommRingCat.of R)) :
    (chartMorphism0 r).base y ∈ Set.range localChart0.base := by
  rw [chartMorphism0]
  exact ⟨_, rfl⟩

/-- chartMorphismInf 的像落在 t-chart 内。 -/
theorem chartMorphismInf_mem_chartInf {R : Type} [CommRing R] [Algebra ℚ R] (r : R)
    (y : Spec (CommRingCat.of R)) :
    (chartMorphismInf r).base y ∈ Set.range localChartInf.base := by
  rw [chartMorphismInf]
  exact ⟨_, rfl⟩


/-! ## chart 坐标的 ℚ-代数相容性 -/

theorem chart_coord_compat {R K : Type} [CommRing R] [Algebra ℚ R] [Field K] [Algebra R K]
    [Algebra ℚ K] [IsScalarTower ℚ R K]
    {i₁ : Spec (CommRingCat.of K) ⟶ projectiveLineGlued}
    {i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ)}
    (hw : i₁ ≫ p1GluedToBase = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂)
    (hi₂ : Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) = i₂)
    (c : chart0Scheme ⟶ projectiveLineGlued) [IsOpenImmersion c]
    (hc : c ≫ p1GluedToBase = chartBase)
    (g : Spec (CommRingCat.of K) ⟶ chart0Scheme) (hg : g ≫ c = i₁) :
    ∀ a : ℚ, (Spec.preimage g).hom (Polynomial.C a) = algebraMap ℚ K a := by
  intro a
  have h1 : g ≫ chartBase = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
    calc g ≫ chartBase = g ≫ (c ≫ p1GluedToBase) := by rw [hc]
      _ = (g ≫ c) ≫ p1GluedToBase := by rw [Category.assoc]
      _ = i₁ ≫ p1GluedToBase := by rw [hg]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := hw
  have hpre := congrArg Spec.preimage h1
  simp only [Spec.preimage_comp, Spec.preimage_map] at hpre
  rw [← hi₂, Spec.preimage_map] at hpre
  have hh := congrArg CommRingCat.Hom.hom hpre
  have hval := RingHom.congr_fun hh a
  simpa [Polynomial.C_eq_algebraMap, CommRingCat.ofHom_comp, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply] using hval


/-! ## 存在性 -/

section Existence

theorem valuativeCriterion_existence :
    ValuativeCriterion.Existence (Mzk1P1ProperActual.p1GluedToBase) := by
  intro S
  let ψR : ℚ →+* S.R := (Spec.preimage S.i₂).hom
  letI : Algebra ℚ S.R := ψR.toAlgebra
  let ψK : ℚ →+* S.K := (algebraMap S.R S.K).comp ψR
  letI : Algebra ℚ S.K := ψK.toAlgebra
  haveI hST : IsScalarTower ℚ S.R S.K :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hi₂ : Spec.map (CommRingCat.ofHom (algebraMap ℚ S.R)) = S.i₂ := by
    have h : CommRingCat.ofHom (algebraMap ℚ S.R) = Spec.preimage S.i₂ := rfl
    rw [h, Spec.map_preimage]
  set w : projectiveLineGlued := S.i₁.base default with hw
  have hwr : Set.range S.i₁.base = {w} := range_eq_singleton_specField S.i₁
  have hcover : w ∈ localChart0.opensRange ∨ w ∈ localChartInf.opensRange := by
    have h : w ∈ localChart0.opensRange ⊔ localChartInf.opensRange := by
      rw [localChart0_opensRange_sup_localChartInf]
      exact TopologicalSpace.Opens.mem_top w
    change w ∈ (localChart0.opensRange : Set projectiveLineGlued) ∪
      localChartInf.opensRange at h
    exact h
  by_cases h0 : w ∈ localChart0.opensRange
  · have hsub : Set.range S.i₁.base ⊆ Set.range localChart0.base := by
      rw [hwr]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h0
    let g0 : Spec (CommRingCat.of S.K) ⟶ chart0Scheme :=
      IsOpenImmersion.lift localChart0 S.i₁ hsub
    have hg0 : g0 ≫ localChart0 = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    have hcompat := chart_coord_compat (R := S.R) (K := S.K) S.commSq.w hi₂
      localChart0 (localChart0_p1GluedToBase) g0 hg0
    set lam : S.K := (Spec.preimage g0).hom Polynomial.X with hlam
    have hi1 : S.i₁ = chartMorphism0 lam := by
      have h := eq_chartMorphism0_of_lift g0 hg0 hcompat
      simpa [hlam] using h
    have hnorm := ValuationRing.isInteger_or_isInteger (R := S.R) (K := S.K) lam
    by_cases hint : IsLocalization.IsInteger S.R lam
    · obtain ⟨r, hr⟩ := hint
      refine ⟨⟨chartMorphism0 r, ?_, ?_⟩⟩
      · calc Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ chartMorphism0 r
            = chartMorphism0 (algebraMap S.R S.K r) := specMap_comp_chartMorphism0 r
          _ = chartMorphism0 lam := by rw [hr]
          _ = S.i₁ := hi1.symm
      · exact Subsingleton.elim _ _
    · have hint2 : IsLocalization.IsInteger S.R lam⁻¹ := hnorm.resolve_left hint
      obtain ⟨r, hr⟩ := hint2
      have hne : lam ≠ 0 := by
        intro h₀
        exact hint ⟨0, by rw [map_zero, h₀]⟩
      refine ⟨⟨chartMorphismInf r, ?_, ?_⟩⟩
      · calc Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ chartMorphismInf r
            = chartMorphismInf (algebraMap S.R S.K r) := specMap_comp_chartMorphismInf r
          _ = chartMorphismInf lam⁻¹ := by rw [hr]
          _ = chartMorphism0 lam := by
              have htr := chartMorphism_transition (R := S.K) (Units.mk0 lam hne)
              simpa using htr.symm
          _ = S.i₁ := hi1.symm
      · exact Subsingleton.elim _ _
  · have hinf : w ∈ localChartInf.opensRange := by
      rcases hcover with h | h
      · exact absurd h h0
      · exact h
    have hsub : Set.range S.i₁.base ⊆ Set.range localChartInf.base := by
      rw [hwr]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hinf
    let g : Spec (CommRingCat.of S.K) ⟶ chartInfScheme :=
      IsOpenImmersion.lift localChartInf S.i₁ hsub
    have hg : g ≫ localChartInf = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    have hcompat := chart_coord_compat (R := S.R) (K := S.K) S.commSq.w hi₂
      localChartInf (localChartInf_p1GluedToBase) g hg
    set tt : S.K := (Spec.preimage g).hom Polynomial.X with htt
    have hi1 : S.i₁ = chartMorphismInf tt := by
      have h := eq_chartMorphismInf_of_lift g hg hcompat
      simpa [htt] using h
    have hzero : tt = 0 := by
      by_contra hne
      have htr := chartMorphism_transition (R := S.K) (Units.mk0 tt⁻¹ (inv_ne_zero hne))
      have hi0 : S.i₁ = chartMorphism0 tt⁻¹ := by
        rw [hi1]
        simpa using htr.symm
      have hwmem : w ∈ Set.range localChart0.base := by
        have hmem := chartMorphism0_mem_chart0 tt⁻¹ (default : Spec (CommRingCat.of S.K))
        rwa [show (chartMorphism0 tt⁻¹).base default = w from by rw [← hi0]] at hmem
      exact h0 hwmem
    refine ⟨⟨chartMorphismInf (0 : S.R), ?_, ?_⟩⟩
    · calc Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ chartMorphismInf (0 : S.R)
          = chartMorphismInf (algebraMap S.R S.K 0) := specMap_comp_chartMorphismInf 0
        _ = chartMorphismInf tt := by rw [map_zero, hzero]
        _ = S.i₁ := hi1.symm
    · exact Subsingleton.elim _ _

end Existence

#print axioms range_eq_singleton_specField
#print axioms range_subset_of_closedPoint_mem
#print axioms specMap_eq_of_comp_eq
#print axioms eq_chartMorphism0_of_lift
#print axioms chart_coord_compat
#print axioms valuativeCriterion_existence
end LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeActual