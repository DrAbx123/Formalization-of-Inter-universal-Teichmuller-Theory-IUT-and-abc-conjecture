/- P¹ glued 的 valuative uniqueness：基础引理批。
   依据 lead 工程建议：uniqueness 独立成文件，import 已绿的 Mzk1P1ValuativeActual，
   保持主文件绿色。 -/
import tmp.sheaf.xif.paper.Mzk1P1ValuativeActual
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeUniquenessActual
open LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeActual

/-! ## chart 态射的单射性 -/

theorem chartMorphism0_injective {K : Type} [Field K] [Algebra ℚ K] {a b : K}
    (h : chartMorphism0 a = chartMorphism0 b) : a = b := by
  haveI : Mono localChart0 := IsOpenImmersion.mono localChart0
  have h2 : Spec.map (CommRingCat.ofHom (evalAt a)) =
      Spec.map (CommRingCat.ofHom (evalAt b)) := by
    have h' : Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChart0 =
        Spec.map (CommRingCat.ofHom (evalAt b)) ≫ localChart0 := h
    exact (cancel_mono localChart0).mp h'
  have h3 : CommRingCat.ofHom (evalAt a) = CommRingCat.ofHom (evalAt b) :=
    Spec.map_injective h2
  have h4 : evalAt a = evalAt b := congrArg CommRingCat.Hom.hom h3
  have := RingHom.congr_fun h4 Polynomial.X
  simpa [evalAt_X] using this

theorem chartMorphismInf_injective {K : Type} [Field K] [Algebra ℚ K] {a b : K}
    (h : chartMorphismInf a = chartMorphismInf b) : a = b := by
  haveI : Mono localChartInf := IsOpenImmersion.mono localChartInf
  have h2 : Spec.map (CommRingCat.ofHom (evalAt a)) =
      Spec.map (CommRingCat.ofHom (evalAt b)) := by
    have h' : Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChartInf =
        Spec.map (CommRingCat.ofHom (evalAt b)) ≫ localChartInf := h
    exact (cancel_mono localChartInf).mp h'
  have h3 : CommRingCat.ofHom (evalAt a) = CommRingCat.ofHom (evalAt b) :=
    Spec.map_injective h2
  have h4 : evalAt a = evalAt b := congrArg CommRingCat.Hom.hom h3
  have := RingHom.congr_fun h4 Polynomial.X
  simpa [evalAt_X] using this

/-! ## 仿射 lift 的坐标相容与分解 -/

/-- lift 经 chart 分解时，其坐标环同态在常数上是 ℚ-代数的。 -/
theorem chart_coord_compat_lift {R : Type} [CommRing R] [Algebra ℚ R]
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ))
    (hi₂ : Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) = i₂)
    (l : Spec (CommRingCat.of R) ⟶ projectiveLineGlued)
    (hl2 : l ≫ p1GluedToBase = i₂)
    (c : chart0Scheme ⟶ projectiveLineGlued) [IsOpenImmersion c]
    (hc : c ≫ p1GluedToBase = chartBase)
    (u : Spec (CommRingCat.of R) ⟶ chart0Scheme) (hu : u ≫ c = l) :
    ∀ a : ℚ, (Spec.preimage u).hom (Polynomial.C a) = algebraMap ℚ R a := by
  intro a
  have h1 : u ≫ chartBase = i₂ := by
    calc u ≫ chartBase = u ≫ (c ≫ p1GluedToBase) := by rw [hc]
      _ = (u ≫ c) ≫ p1GluedToBase := by rw [Category.assoc]
      _ = l ≫ p1GluedToBase := by rw [hu]
      _ = i₂ := hl2
  have hpre := congrArg Spec.preimage h1
  simp only [Spec.preimage_comp, Spec.preimage_map] at hpre
  rw [← hi₂, Spec.preimage_map] at hpre
  have hh := congrArg CommRingCat.Hom.hom hpre
  have hval := RingHom.congr_fun hh a
  simpa [Polynomial.C_eq_algebraMap, CommRingCat.ofHom_comp, RingHom.comp_apply] using hval

/-- 底为一般交换环（带 ℚ-代数结构）时，经 chart0 分解的态射等于 chartMorphism0。 -/
theorem eq_chartMorphism0_of_lift' {R : Type} [CommRing R] [Algebra ℚ R]
    {l : Spec (CommRingCat.of R) ⟶ projectiveLineGlued}
    (g : Spec (CommRingCat.of R) ⟶ chart0Scheme) (hg : g ≫ localChart0 = l)
    (hC : ∀ a : ℚ, (Spec.preimage g).hom (Polynomial.C a) = algebraMap ℚ R a) :
    l = chartMorphism0 ((Spec.preimage g).hom Polynomial.X) := by
  have hhom : (Spec.preimage g).hom = evalAt ((Spec.preimage g).hom Polynomial.X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) (by rw [evalAt_X])
    rw [evalAt_C]
    exact hC a
  set lam : R := (Spec.preimage g).hom Polynomial.X with hlam
  have hg' : g = Spec.map (CommRingCat.ofHom (evalAt lam)) := by
    rw [← Spec.map_preimage g]
    congr 1
    apply CommRingCat.hom_ext
    simpa [hlam] using hhom
  calc l = g ≫ localChart0 := hg.symm
    _ = Spec.map (CommRingCat.ofHom (evalAt lam)) ≫ localChart0 := by rw [hg']
    _ = chartMorphism0 lam := rfl

theorem eq_chartMorphismInf_of_lift' {R : Type} [CommRing R] [Algebra ℚ R]
    {l : Spec (CommRingCat.of R) ⟶ projectiveLineGlued}
    (g : Spec (CommRingCat.of R) ⟶ chartInfScheme) (hg : g ≫ localChartInf = l)
    (hC : ∀ a : ℚ, (Spec.preimage g).hom (Polynomial.C a) = algebraMap ℚ R a) :
    l = chartMorphismInf ((Spec.preimage g).hom Polynomial.X) := by
  have hhom : (Spec.preimage g).hom = evalAt ((Spec.preimage g).hom Polynomial.X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) (by rw [evalAt_X])
    rw [evalAt_C]
    exact hC a
  set lam : R := (Spec.preimage g).hom Polynomial.X with hlam
  have hg' : g = Spec.map (CommRingCat.ofHom (evalAt lam)) := by
    rw [← Spec.map_preimage g]
    congr 1
    apply CommRingCat.hom_ext
    simpa [hlam] using hhom
  calc l = g ≫ localChartInf := hg.symm
    _ = Spec.map (CommRingCat.ofHom (evalAt lam)) ≫ localChartInf := by rw [hg']
    _ = chartMorphismInf lam := rfl

/-- 若 lift 的闭点落在 λ-chart，则它是某个 chartMorphism0。 -/
theorem lift_eq_chartMorphism0_of_closedPoint_mem {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra ℚ R]
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ))
    (hi₂ : Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) = i₂)
    (l : Spec (CommRingCat.of R) ⟶ projectiveLineGlued)
    (hl2 : l ≫ p1GluedToBase = i₂)
    (hmem : l.base (IsLocalRing.closedPoint R) ∈ Set.range localChart0.base) :
    ∃ r : R, l = chartMorphism0 r := by
  have hsub : Set.range l.base ⊆ Set.range localChart0.base :=
    range_subset_of_closedPoint_mem l localChart0 hmem
  let u : Spec (CommRingCat.of R) ⟶ chart0Scheme := IsOpenImmersion.lift localChart0 l hsub
  have hu : u ≫ localChart0 = l := IsOpenImmersion.lift_fac _ _ _
  have hcompat := chart_coord_compat_lift i₂ hi₂ l hl2 localChart0
    (localChart0_p1GluedToBase) u hu
  exact ⟨(Spec.preimage u).hom Polynomial.X, eq_chartMorphism0_of_lift' u hu hcompat⟩

/-- 若 lift 的闭点落在 t-chart，则它是某个 chartMorphismInf。 -/
theorem lift_eq_chartMorphismInf_of_closedPoint_mem {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra ℚ R]
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ))
    (hi₂ : Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) = i₂)
    (l : Spec (CommRingCat.of R) ⟶ projectiveLineGlued)
    (hl2 : l ≫ p1GluedToBase = i₂)
    (hmem : l.base (IsLocalRing.closedPoint R) ∈ Set.range localChartInf.base) :
    ∃ r : R, l = chartMorphismInf r := by
  have hsub : Set.range l.base ⊆ Set.range localChartInf.base :=
    range_subset_of_closedPoint_mem l localChartInf hmem
  let u : Spec (CommRingCat.of R) ⟶ chartInfScheme := IsOpenImmersion.lift localChartInf l hsub
  have hu : u ≫ localChartInf = l := IsOpenImmersion.lift_fac _ _ _
  have hcompat := chart_coord_compat_lift i₂ hi₂ l hl2 localChartInf
    (localChartInf_p1GluedToBase) u hu
  exact ⟨(Spec.preimage u).hom Polynomial.X, eq_chartMorphismInf_of_lift' u hu hcompat⟩




/-- ∞ 点（chartMorphismInf 0）与有限点 0（chartMorphism0 0）不同。 -/
theorem chartMorphismInf_zero_ne_chartMorphism0_zero {K : Type} [Field K] [Algebra ℚ K] :
    chartMorphismInf (0 : K) ≠ chartMorphism0 (0 : K) := by
  intro h
  have hw : (chartMorphismInf (0 : K)).base default = (chartMorphism0 (0 : K)).base default :=
    congrArg (fun m => m.base default) h
  set x0 : ↥(Spec (CommRingCat.of (Polynomial ℚ))) :=
    (Spec.map (CommRingCat.ofHom (evalAt (0 : K)))).base default with hx0
  have hL : (chartMorphismInf (0 : K)).base default = localChartInf.base x0 := by
    rw [chartMorphismInf, hx0]
    rfl
  have hR : (chartMorphism0 (0 : K)).base default = localChart0.base x0 := by
    rw [chartMorphism0, hx0]
    rfl
  have hp : localChartInf.base x0 = localChart0.base x0 := by
    rw [← hL, hw, hR]
  obtain ⟨y, hy⟩ : localChartInf.base x0 ∈ Set.range localChart0.base := ⟨x0, hp.symm⟩
  have hrel : p1GlueData.Rel ⟨ULift.up false, y⟩ ⟨ULift.up true, x0⟩ :=
    (p1GlueData.ι_eq_iff (ULift.up false) (ULift.up true) y x0).mp hy
  obtain ⟨z, -, hz⟩ := hrel
  have hz' : PrimeSpectrum.comap (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing))
      (z : PrimeSpectrum OverlapRing) = (x0 : PrimeSpectrum (Polynomial ℚ)) := by
    have h1 : (overlapToChartInf : ↥(Spec (CommRingCat.of OverlapRing)) →
        ↥(Spec (CommRingCat.of (Polynomial ℚ)))) z = x0 := hz
    rw [overlapToChartInf] at h1
    rw [Spec.map_apply] at h1
    exact h1
  have hXimg : (Polynomial.X) ∈
      ((Spec.map (CommRingCat.ofHom (evalAt (0 : K)))).base default :
        PrimeSpectrum (Polynomial ℚ)).asIdeal := by
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    change (evalAt (0 : K)) (Polynomial.X) ∈
      ((default : Spec (CommRingCat.of K)) : PrimeSpectrum K).asIdeal
    rw [evalAt_X]
    exact Ideal.zero_mem _
  have hX : (Polynomial.X) ∈ (x0 : PrimeSpectrum (Polynomial ℚ)).asIdeal := by
    rw [hx0]
    exact hXimg
  have hXz : (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) (Polynomial.X) ∈
      (z : PrimeSpectrum OverlapRing).asIdeal := by
    have h2 : (Polynomial.X) ∈
        (PrimeSpectrum.comap (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing))
          (z : PrimeSpectrum OverlapRing)).asIdeal := by
      rw [hz']
      exact hX
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h2
    exact h2
  have hval : (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) (Polynomial.X) = invLambda := by
    rw [RingHom.comp_apply]
    rw [show algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X) = ovLambda from rfl]
    exact invAuto_ovLambda
  rw [hval] at hXz
  exact (z : PrimeSpectrum OverlapRing).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hXz invLambda_isUnit)


/-! ## 唯一性 -/

theorem valuativeCriterion_uniqueness :
    ValuativeCriterion.Uniqueness (Mzk1P1ProperActual.p1GluedToBase) := by
  intro S
  refine ⟨fun L1 L2 => ?_⟩
  let ψR : ℚ →+* S.R := (Spec.preimage S.i₂).hom
  letI : Algebra ℚ S.R := ψR.toAlgebra
  let ψK : ℚ →+* S.K := (algebraMap S.R S.K).comp ψR
  letI : Algebra ℚ S.K := ψK.toAlgebra
  haveI hST : IsScalarTower ℚ S.R S.K :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hi₂ : Spec.map (CommRingCat.ofHom (algebraMap ℚ S.R)) = S.i₂ := by
    have h : CommRingCat.ofHom (algebraMap ℚ S.R) = Spec.preimage S.i₂ := rfl
    rw [h, Spec.map_preimage]
  set sc : Spec (CommRingCat.of S.R) := IsLocalRing.closedPoint S.R with hsc
  set w : projectiveLineGlued := S.i₁.base default with hwdef
  have hwr : Set.range S.i₁.base = {w} := range_eq_singleton_specField S.i₁
  have hcov : ∀ (L : S.commSq.LiftStruct),
      L.l.base sc ∈ Set.range localChart0.base ∨ L.l.base sc ∈ Set.range localChartInf.base := by
    intro L
    have h : L.l.base sc ∈ localChart0.opensRange ⊔ localChartInf.opensRange := by
      rw [localChart0_opensRange_sup_localChartInf]
      exact TopologicalSpace.Opens.mem_top _
    change L.l.base sc ∈ (localChart0.opensRange : Set projectiveLineGlued) ∪
      localChartInf.opensRange at h
    exact h
  have rep0 : ∀ (L : S.commSq.LiftStruct), L.l.base sc ∈ Set.range localChart0.base →
      ∃ r : S.R, L.l = chartMorphism0 r := by
    intro L hL
    exact lift_eq_chartMorphism0_of_closedPoint_mem S.i₂ hi₂ L.l L.fac_right hL
  have repInf : ∀ (L : S.commSq.LiftStruct), L.l.base sc ∈ Set.range localChartInf.base →
      ∃ r : S.R, L.l = chartMorphismInf r := by
    intro L hL
    exact lift_eq_chartMorphismInf_of_closedPoint_mem S.i₂ hi₂ L.l L.fac_right hL
  by_cases hw0 : w ∈ localChart0.opensRange
  · -- ===== 主情形 A: w ∈ λ-chart =====
    have hsub : Set.range S.i₁.base ⊆ Set.range localChart0.base := by
      rw [hwr]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hw0
    let g : Spec (CommRingCat.of S.K) ⟶ chart0Scheme :=
      IsOpenImmersion.lift localChart0 S.i₁ hsub
    have hg : g ≫ localChart0 = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    have hcompat := chart_coord_compat (R := S.R) (K := S.K) S.commSq.w hi₂ localChart0
      (localChart0_p1GluedToBase) g hg
    set lam : S.K := (Spec.preimage g).hom Polynomial.X with hlam
    have hi1 : S.i₁ = chartMorphism0 lam := by
      have h := eq_chartMorphism0_of_lift g hg hcompat
      simpa [hlam] using h
    have key0 : ∀ (L : S.commSq.LiftStruct), L.l.base sc ∈ Set.range localChart0.base →
        ∃ r : S.R, L.l = chartMorphism0 r ∧ algebraMap S.R S.K r = lam := by
      intro L hL
      obtain ⟨r, hr⟩ := rep0 L hL
      refine ⟨r, hr, ?_⟩
      refine chartMorphism0_injective ?_
      calc chartMorphism0 (algebraMap S.R S.K r)
          = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ L.l := by
            rw [hr, specMap_comp_chartMorphism0]
        _ = S.i₁ := L.fac_left
        _ = chartMorphism0 lam := hi1
    have keyInf : ∀ (L : S.commSq.LiftStruct),
        (hL : L.l.base sc ∈ Set.range localChartInf.base) → lam ≠ 0 →
        ∃ r : S.R, L.l = chartMorphismInf r ∧ algebraMap S.R S.K r = lam⁻¹ := by
      intro L hL hne
      obtain ⟨r, hr⟩ := repInf L hL
      refine ⟨r, hr, ?_⟩
      refine chartMorphismInf_injective ?_
      have hEq : chartMorphismInf (algebraMap S.R S.K r) = chartMorphism0 lam := by
        calc chartMorphismInf (algebraMap S.R S.K r)
            = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ L.l := by
              rw [hr, specMap_comp_chartMorphismInf]
          _ = S.i₁ := L.fac_left
          _ = chartMorphism0 lam := hi1
      have htr : chartMorphism0 lam = chartMorphismInf lam⁻¹ := by
        have := chartMorphism_transition (R := S.K) (Units.mk0 lam hne)
        simpa using this
      rw [hEq, htr]
    have keyInf0 : ∀ (L : S.commSq.LiftStruct),
        (hL : L.l.base sc ∈ Set.range localChartInf.base) → lam = 0 → False := by
      intro L hL h0
      obtain ⟨r, hr⟩ := repInf L hL
      have hEq : chartMorphismInf (algebraMap S.R S.K r) = chartMorphism0 0 := by
        calc chartMorphismInf (algebraMap S.R S.K r)
            = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ L.l := by
              rw [hr, specMap_comp_chartMorphismInf]
          _ = S.i₁ := L.fac_left
          _ = chartMorphism0 lam := hi1
          _ = chartMorphism0 0 := by rw [h0]
      by_cases hr0 : algebraMap S.R S.K r = 0
      · rw [hr0] at hEq
        exact chartMorphismInf_zero_ne_chartMorphism0_zero hEq
      · have htr : chartMorphismInf (algebraMap S.R S.K r) =
            chartMorphism0 (algebraMap S.R S.K r)⁻¹ := by
          have h2 := chartMorphism_transition (R := S.K)
            (Units.mk0 (algebraMap S.R S.K r)⁻¹ (inv_ne_zero hr0))
          simpa using h2.symm
        rw [htr] at hEq
        exact absurd (chartMorphism0_injective hEq) (inv_ne_zero hr0)
    have hnorm := ValuationRing.isInteger_or_isInteger (R := S.R) (K := S.K) lam
    by_cases hint : IsLocalization.IsInteger S.R lam
    · obtain ⟨r0, hr0⟩ := hint
      have all0 : ∀ (L : S.commSq.LiftStruct), L.l = chartMorphism0 r0 := by
        intro L
        by_cases hL0 : L.l.base sc ∈ Set.range localChart0.base
        · obtain ⟨r, hr, har⟩ := key0 L hL0
          have hrr : r = r0 := IsFractionRing.injective S.R S.K (by rw [har, hr0])
          rw [hr, hrr]
        · have hLinf : L.l.base sc ∈ Set.range localChartInf.base := (hcov L).resolve_left hL0
          by_cases h0 : lam = 0
          · exact absurd h0 (keyInf0 L hLinf)
          · obtain ⟨r, hr, har⟩ := keyInf L hLinf h0
            have hr0ne : r0 ≠ 0 := by
              intro hh
              have hh' := congrArg (algebraMap S.R S.K) hh
              rw [map_zero, hr0] at hh'
              exact h0 hh'
            have hprod : r * r0 = 1 := by
              apply IsFractionRing.injective S.R S.K
              rw [map_mul, map_one, har, hr0, inv_mul_cancel₀ h0]
            rw [hr]
            have hrev : r0 * r = 1 := by rw [mul_comm]; exact hprod
            let u : S.Rˣ := ⟨r0, r, hrev, hprod⟩
            have htr := chartMorphism_transition (R := S.R) u
            change chartMorphism0 r0 = chartMorphismInf r at htr
            exact htr.symm
      exact CommSq.LiftStruct.ext (by rw [all0 L1, all0 L2])
    · have hint2 : IsLocalization.IsInteger S.R lam⁻¹ := hnorm.resolve_left hint
      obtain ⟨r0, hr0⟩ := hint2
      have hne : lam ≠ 0 := by
        intro h0
        exact hint ⟨0, by rw [map_zero, h0]⟩
      have no0 : ∀ (L : S.commSq.LiftStruct),
          ¬ (L.l.base sc ∈ Set.range localChart0.base) := by
        intro L hL
        obtain ⟨r, -, har⟩ := key0 L hL
        exact hint ⟨r, har⟩
      have allInf : ∀ (L : S.commSq.LiftStruct), L.l = chartMorphismInf r0 := by
        intro L
        have hLinf : L.l.base sc ∈ Set.range localChartInf.base :=
          (hcov L).resolve_left (no0 L)
        obtain ⟨r, hr, har⟩ := keyInf L hLinf hne
        have hrr : r = r0 := IsFractionRing.injective S.R S.K (by rw [har, hr0])
        rw [hr, hrr]
      exact CommSq.LiftStruct.ext (by rw [allInf L1, allInf L2])
  · -- ===== 主情形 B: w ∈ t-chart =====
    have hwinf : w ∈ localChartInf.opensRange := by
      rcases localChart_jointly_surjective w with h | h
      · exact absurd h hw0
      · exact h
    have hsub : Set.range S.i₁.base ⊆ Set.range localChartInf.base := by
      rw [hwr]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hwinf
    let g : Spec (CommRingCat.of S.K) ⟶ chartInfScheme :=
      IsOpenImmersion.lift localChartInf S.i₁ hsub
    have hg : g ≫ localChartInf = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    have hcompat := chart_coord_compat (R := S.R) (K := S.K) S.commSq.w hi₂ localChartInf
      (localChartInf_p1GluedToBase) g hg
    set tau : S.K := (Spec.preimage g).hom Polynomial.X with htau
    have hi1 : S.i₁ = chartMorphismInf tau := by
      have h := eq_chartMorphismInf_of_lift g hg hcompat
      simpa [htau] using h
    have keyInf2 : ∀ (L : S.commSq.LiftStruct), L.l.base sc ∈ Set.range localChartInf.base →
        ∃ r : S.R, L.l = chartMorphismInf r ∧ algebraMap S.R S.K r = tau := by
      intro L hL
      obtain ⟨r, hr⟩ := repInf L hL
      refine ⟨r, hr, ?_⟩
      refine chartMorphismInf_injective ?_
      calc chartMorphismInf (algebraMap S.R S.K r)
          = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ L.l := by
            rw [hr, specMap_comp_chartMorphismInf]
        _ = S.i₁ := L.fac_left
        _ = chartMorphismInf tau := hi1
    have key0_2 : ∀ (L : S.commSq.LiftStruct),
        (hL : L.l.base sc ∈ Set.range localChart0.base) → tau ≠ 0 →
        ∃ r : S.R, L.l = chartMorphism0 r ∧ algebraMap S.R S.K r = tau⁻¹ := by
      intro L hL htne
      obtain ⟨r, hr⟩ := rep0 L hL
      refine ⟨r, hr, ?_⟩
      have hEq : chartMorphism0 (algebraMap S.R S.K r) = chartMorphismInf tau := by
        calc chartMorphism0 (algebraMap S.R S.K r)
            = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ L.l := by
              rw [hr, specMap_comp_chartMorphism0]
          _ = S.i₁ := L.fac_left
          _ = chartMorphismInf tau := hi1
      have htr : chartMorphismInf tau = chartMorphism0 tau⁻¹ := by
        have h2 := chartMorphism_transition (R := S.K)
          (Units.mk0 tau⁻¹ (inv_ne_zero htne))
        simpa using h2.symm
      refine chartMorphism0_injective ?_
      rw [hEq, htr]
    by_cases htau0 : tau = 0
    · have allInf0 : ∀ (L : S.commSq.LiftStruct), L.l = chartMorphismInf (0 : S.R) := by
        intro L
        rcases hcov L with hL0 | hLinf
        · exfalso
          obtain ⟨r, hr⟩ := rep0 L hL0
          have hEq : chartMorphism0 (algebraMap S.R S.K r) = chartMorphismInf (0 : S.K) := by
            calc chartMorphism0 (algebraMap S.R S.K r)
                = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ L.l := by
                  rw [hr, specMap_comp_chartMorphism0]
              _ = S.i₁ := L.fac_left
              _ = chartMorphismInf tau := hi1
              _ = chartMorphismInf 0 := by rw [htau0]
          by_cases hr0 : algebraMap S.R S.K r = 0
          · rw [hr0] at hEq
            exact chartMorphismInf_zero_ne_chartMorphism0_zero hEq.symm
          · have htr : chartMorphism0 (algebraMap S.R S.K r) =
                chartMorphismInf (algebraMap S.R S.K r)⁻¹ := by
              have h2 := chartMorphism_transition (R := S.K)
                (Units.mk0 (algebraMap S.R S.K r) hr0)
              simpa using h2
            rw [htr] at hEq
            exact absurd (chartMorphismInf_injective hEq) (inv_ne_zero hr0)
        · obtain ⟨r, hr, har⟩ := keyInf2 L hLinf
          have hrr : r = 0 := by
            apply IsFractionRing.injective S.R S.K
            rw [map_zero, har, htau0]
          rw [hr, hrr]
      exact CommSq.LiftStruct.ext (by rw [allInf0 L1, allInf0 L2])
    · have hnorm := ValuationRing.isInteger_or_isInteger (R := S.R) (K := S.K) tau
      by_cases hint : IsLocalization.IsInteger S.R tau
      · obtain ⟨r0, hr0⟩ := hint
        have hr0ne : r0 ≠ 0 := by
          intro hh
          have hh' := congrArg (algebraMap S.R S.K) hh
          rw [map_zero, hr0] at hh'
          exact htau0 hh'
        have allInf : ∀ (L : S.commSq.LiftStruct), L.l = chartMorphismInf r0 := by
          intro L
          by_cases hL0 : L.l.base sc ∈ Set.range localChart0.base
          · obtain ⟨r, hr, har⟩ := key0_2 L hL0 htau0
            have hprod : r * r0 = 1 := by
              apply IsFractionRing.injective S.R S.K
              rw [map_mul, map_one, har, hr0]
              field_simp
            rw [hr]
            have hrev : r0 * r = 1 := by rw [mul_comm]; exact hprod
            let u : S.Rˣ := ⟨r, r0, hprod, hrev⟩
            have htr := chartMorphism_transition (R := S.R) u
            change chartMorphism0 r = chartMorphismInf r0 at htr
            exact htr
          · have hLinf : L.l.base sc ∈ Set.range localChartInf.base :=
              (hcov L).resolve_left hL0
            obtain ⟨r, hr, har⟩ := keyInf2 L hLinf
            have hrr : r = r0 := IsFractionRing.injective S.R S.K (by rw [har, hr0])
            rw [hr, hrr]
        exact CommSq.LiftStruct.ext (by rw [allInf L1, allInf L2])
      · have hint2 : IsLocalization.IsInteger S.R tau⁻¹ := hnorm.resolve_left hint
        obtain ⟨r0, hr0⟩ := hint2
        have noInf : ∀ (L : S.commSq.LiftStruct),
            ¬ (L.l.base sc ∈ Set.range localChartInf.base) := by
          intro L hL
          obtain ⟨r, -, har⟩ := keyInf2 L hL
          exact hint ⟨r, har⟩
        have all0 : ∀ (L : S.commSq.LiftStruct), L.l = chartMorphism0 r0 := by
          intro L
          have hL0 : L.l.base sc ∈ Set.range localChart0.base :=
            (hcov L).resolve_right (noInf L)
          obtain ⟨r, hr, har⟩ := key0_2 L hL0 htau0
          have hrr : r = r0 := IsFractionRing.injective S.R S.K (by rw [har, hr0])
          rw [hr, hrr]
        exact CommSq.LiftStruct.ext (by rw [all0 L1, all0 L2])


/-- 契约主定理：P¹（glued 两 chart 模型）满足 valuative criterion（存在+唯一）。 -/
theorem p1GluedToBase_valuativeCriterion :
    ValuativeCriterion (Mzk1P1ProperActual.p1GluedToBase) :=
  ValuativeCriterion.iff.mpr
    ⟨Mzk1P1ValuativeActual.valuativeCriterion_existence, valuativeCriterion_uniqueness⟩

#print axioms valuativeCriterion_uniqueness
#print axioms p1GluedToBase_valuativeCriterion

end LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeUniquenessActual
