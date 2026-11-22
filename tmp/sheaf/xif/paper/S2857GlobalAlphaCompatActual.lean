/-
S2857: the four-case compatibility for the global chart-alpha morphism.

The global chart-alpha morphism of the fixed E37 projective scheme is
prescribed on the two charts by

* chart Z: `S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K`,
* chart Y: `chartYNegGlued K`.

These two prescriptions must agree on all four intersections of the two
charts of the glue data `D K = E37ProjGlueData K (S2820E37TransitionIso K)`:

* (Z,Z) and (Y,Y): the chart maps are open immersions, hence monomorphisms,
  so the two pullback projections coincide;
* (Z,Y): on the chart-Z overlap the chart-Z negation endomorphism agrees with
  the chart-Y negation (the ring identity `psi ∘ g1Ring = algebraMap ∘ S2853RingHom`,
  obtained from `g1Ring_eq_alpha_chartZNeg` and `psi_comp_alpha`);
* (Y,Z): follows from (Z,Y) by pullback symmetry.

The resulting `globalAlphaCompat` is the compatibility datum of
`globalAlphaComp K`, and `globalAlpha K (globalAlphaCompat K)` is the glued
self-map of `S2820E37ProjectiveScheme K`.
-/

import tmp.sheaf.xif.paper.S2857GlobalAlphaActual
import tmp.sheaf.xif.paper.S2856HfOverlapActual
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual
import tmp.sheaf.xif.paper.S2856HfYZRingActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2856HfYZRingActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual

variable (K : Type) [Field K] [DecidableEq K]

/-! ## 1. The two chart maps are open immersions -/

/-- The chart-Z map into the glued projective scheme is a monomorphism. -/
theorem chartZMap_mono : Mono (S2820E37ChartZMap K) := by
  haveI : IsOpenImmersion (S2820E37ChartZMap K) :=
    (D K).ι_isOpenImmersion (ULift.up false)
  exact IsOpenImmersion.mono (S2820E37ChartZMap K)

/-- The chart-Y map into the glued projective scheme is a monomorphism. -/
theorem chartYMap_mono : Mono (S2820E37ChartYMap K) := by
  haveI : IsOpenImmersion (S2820E37ChartYMap K) :=
    (D K).ι_isOpenImmersion (ULift.up true)
  exact IsOpenImmersion.mono (S2820E37ChartYMap K)

/-! ## 2. The chart-Z overlap as the pullback of the two chart maps -/

/-- The chart-Z overlap maps canonically to the pullback of the two charts. -/
noncomputable def chartOverlapToPullback :
    E37ChartZOverlap K ⟶
      pullback (S2820E37ChartZMap K) (S2820E37ChartYMap K) :=
  pullback.lift (E37ChartZOverlapMap K)
    ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K)
    ((D K).vPullbackCone (ULift.up false) (ULift.up true)).condition

/-- Conversely, the pullback of the two chart maps projects to the chart-Z
overlap (the pullback cone of the glue data). -/
noncomputable def pullbackToChartOverlap :
    pullback (S2820E37ChartZMap K) (S2820E37ChartYMap K) ⟶ E37ChartZOverlap K :=
  PullbackCone.IsLimit.lift
    ((D K).vPullbackConeIsLimit (ULift.up false) (ULift.up true))
    (pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K))
    (pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K))
    pullback.condition

theorem chartOverlapToPullback_fst :
    chartOverlapToPullback K ≫
        pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) =
      E37ChartZOverlapMap K :=
  pullback.lift_fst _ _ _

theorem chartOverlapToPullback_snd :
    chartOverlapToPullback K ≫
        pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) =
      (S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K :=
  pullback.lift_snd _ _ _

theorem pullbackToChartOverlap_fst :
    pullbackToChartOverlap K ≫ E37ChartZOverlapMap K =
      pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) :=
  PullbackCone.IsLimit.lift_fst
    ((D K).vPullbackConeIsLimit (ULift.up false) (ULift.up true)) _ _ _

theorem pullbackToChartOverlap_snd :
    pullbackToChartOverlap K ≫
        ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K) =
      pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) :=
  PullbackCone.IsLimit.lift_snd
    ((D K).vPullbackConeIsLimit (ULift.up false) (ULift.up true)) _ _ _

/-- The chart-Z overlap is the pullback of the two chart maps. -/
noncomputable def chartOverlapPullbackIso :
    E37ChartZOverlap K ≅ pullback (S2820E37ChartZMap K) (S2820E37ChartYMap K) where
  hom := chartOverlapToPullback K
  inv := pullbackToChartOverlap K
  hom_inv_id := by
    apply PullbackCone.IsLimit.hom_ext
      ((D K).vPullbackConeIsLimit (ULift.up false) (ULift.up true))
    · show (chartOverlapToPullback K ≫ pullbackToChartOverlap K) ≫ E37ChartZOverlapMap K =
        𝟙 (E37ChartZOverlap K) ≫ E37ChartZOverlapMap K
      rw [Category.assoc, pullbackToChartOverlap_fst, chartOverlapToPullback_fst,
        Category.id_comp]
    · show (chartOverlapToPullback K ≫ pullbackToChartOverlap K) ≫
          ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K) =
        𝟙 (E37ChartZOverlap K) ≫ ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K)
      rw [Category.assoc, pullbackToChartOverlap_snd, chartOverlapToPullback_snd,
        Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · show (pullbackToChartOverlap K ≫ chartOverlapToPullback K) ≫
          pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) =
        𝟙 (pullback (S2820E37ChartZMap K) (S2820E37ChartYMap K)) ≫
          pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K)
      rw [Category.assoc, chartOverlapToPullback_fst, pullbackToChartOverlap_fst,
        Category.id_comp]
    · show (pullbackToChartOverlap K ≫ chartOverlapToPullback K) ≫
          pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) =
        𝟙 (pullback (S2820E37ChartZMap K) (S2820E37ChartYMap K)) ≫
          pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K)
      rw [Category.assoc, chartOverlapToPullback_snd, pullbackToChartOverlap_snd,
        Category.id_comp]

/-! ## 3. The ring comparison on the chart-Z overlap -/

/-- The chart-Y projection of the chart-Y negation, composed with the
chart-Z transition, is the chart-Z negation endomorphism: this is the
ring-level identity `psi ∘ g1Ring = algebraMap ∘ S2853RingHom`. -/
theorem psi_comp_g1Ring :
    (psi K).comp (g1Ring K) =
      (algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K)).comp
        (S2853RingHom K) := by
  rw [g1Ring_eq_alpha_chartZNeg K, ← RingHom.comp_assoc, psi_comp_alpha]

/-! ## 4. The (Z,Y) compatibility -/

/-- The chart-Y negation restricts to the chart-Z negation on the chart-Z
overlap. -/
theorem chartOverlap_endo_eq :
    E37ChartZOverlapMap K ≫ (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) =
      ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K) ≫ chartYNegGlued K := by
  have hproj : E37ChartYOverlapMap K ≫ chartYNegGlued K = g1Scheme K :=
    (chartYCover K).ι_glueMorphisms (chartYNegGMap K) (hf_pair K) true
  have hL : E37ChartZOverlapMap K ≫ S2853ChartZSchemeEndo K =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K)).comp
          (S2853RingHom K))) :=
    (specMap_comp_ringHom (S2853RingHom K)
      (algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K))).symm
  have hR : (S2820E37TransitionIso K).hom ≫
        Spec.map (CommRingCat.ofHom (g1Ring K)) =
      Spec.map (CommRingCat.ofHom ((psi K).comp (g1Ring K))) :=
    (specMap_comp_ringHom (g1Ring K) (psi K)).symm
  calc
    E37ChartZOverlapMap K ≫ (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K)
        = (E37ChartZOverlapMap K ≫ S2853ChartZSchemeEndo K) ≫
            S2820E37ChartZMap K := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom
          ((algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K)).comp
            (S2853RingHom K))) ≫ S2820E37ChartZMap K := by rw [hL]
    _ = Spec.map (CommRingCat.ofHom ((psi K).comp (g1Ring K))) ≫
          S2820E37ChartZMap K := by rw [psi_comp_g1Ring]
    _ = (Spec.map (CommRingCat.ofHom (psi K)) ≫
          Spec.map (CommRingCat.ofHom (g1Ring K))) ≫ S2820E37ChartZMap K := by
        rw [specMap_comp_ringHom (g1Ring K) (psi K)]
    _ = (S2820E37TransitionIso K).hom ≫
          (Spec.map (CommRingCat.ofHom (g1Ring K)) ≫ S2820E37ChartZMap K) := by
        rw [Category.assoc]
        rfl
    _ = (S2820E37TransitionIso K).hom ≫ g1Scheme K := rfl
    _ = (S2820E37TransitionIso K).hom ≫ (E37ChartYOverlapMap K ≫ chartYNegGlued K) := by
        rw [hproj]
    _ = ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K) ≫ chartYNegGlued K := by
        rw [Category.assoc]

/-- The (chart Z, chart Y) case of the compatibility. -/
theorem compat_false_true :
    pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫
        (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) =
      pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K := by
  have hA : chartOverlapToPullback K ≫
        (pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫
          (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K)) =
      E37ChartZOverlapMap K ≫ (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) := by
    rw [← Category.assoc, chartOverlapToPullback_fst]
  have hB : chartOverlapToPullback K ≫
        (pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K) =
      ((S2820E37TransitionIso K).hom ≫ E37ChartYOverlapMap K) ≫ chartYNegGlued K := by
    rw [← Category.assoc, chartOverlapToPullback_snd]
  have hkey : chartOverlapToPullback K ≫
        (pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫
          (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K)) =
      chartOverlapToPullback K ≫
        (pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K) :=
    hA.trans ((chartOverlap_endo_eq K).trans hB.symm)
  haveI : IsIso (chartOverlapToPullback K) := (chartOverlapPullbackIso K).isIso_hom
  exact (cancel_epi (chartOverlapToPullback K)).mp hkey

/-! ## 5. The (Y,Z) compatibility -/

/-- The (chart Y, chart Z) case of the compatibility, by pullback symmetry. -/
theorem compat_true_false :
    pullback.fst (S2820E37ChartYMap K) (S2820E37ChartZMap K) ≫ chartYNegGlued K =
      pullback.snd (S2820E37ChartYMap K) (S2820E37ChartZMap K) ≫
        (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) := by
  have hA : (pullbackSymmetry (S2820E37ChartZMap K) (S2820E37ChartYMap K)).hom ≫
        (pullback.fst (S2820E37ChartYMap K) (S2820E37ChartZMap K) ≫ chartYNegGlued K) =
      (pullbackSymmetry (S2820E37ChartZMap K) (S2820E37ChartYMap K)).hom ≫
        (pullback.snd (S2820E37ChartYMap K) (S2820E37ChartZMap K) ≫
          (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K)) := by
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      ← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact (compat_false_true K).symm
  have h2 := congrArg
    (fun t => (pullbackSymmetry (S2820E37ChartZMap K) (S2820E37ChartYMap K)).inv ≫ t) hA
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h2

/-! ## 6. The same-chart cases -/

/-- The (chart Z, chart Z) case: the chart-Z map is a monomorphism. -/
theorem compat_ZZ :
    pullback.fst (S2820E37ChartZMap K) (S2820E37ChartZMap K) ≫
        (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) =
      pullback.snd (S2820E37ChartZMap K) (S2820E37ChartZMap K) ≫
        (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) := by
  haveI : Mono (S2820E37ChartZMap K) := chartZMap_mono K
  have hcond : pullback.fst (S2820E37ChartZMap K) (S2820E37ChartZMap K) =
      pullback.snd (S2820E37ChartZMap K) (S2820E37ChartZMap K) :=
    (cancel_mono (S2820E37ChartZMap K)).mp pullback.condition
  rw [hcond]

/-- The (chart Y, chart Y) case: the chart-Y map is a monomorphism. -/
theorem compat_YY :
    pullback.fst (S2820E37ChartYMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K =
      pullback.snd (S2820E37ChartYMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K := by
  haveI : Mono (S2820E37ChartYMap K) := chartYMap_mono K
  have hcond : pullback.fst (S2820E37ChartYMap K) (S2820E37ChartYMap K) =
      pullback.snd (S2820E37ChartYMap K) (S2820E37ChartYMap K) :=
    (cancel_mono (S2820E37ChartYMap K)).mp pullback.condition
  rw [hcond]

/-! ## 7. The four-case compatibility -/

/-- The four-case compatibility for the global chart-alpha morphism. -/
theorem globalAlphaCompat :
    ∀ x y, pullback.fst ((D K).openCover.f x) ((D K).openCover.f y) ≫
        globalAlphaComp K x =
      pullback.snd ((D K).openCover.f x) ((D K).openCover.f y) ≫
        globalAlphaComp K y := by
  intro x y
  cases x with
  | up xb =>
    cases y with
    | up yb =>
      cases xb <;> cases yb
      · change pullback.fst (S2820E37ChartZMap K) (S2820E37ChartZMap K) ≫
            (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) =
          pullback.snd (S2820E37ChartZMap K) (S2820E37ChartZMap K) ≫
            (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K)
        exact compat_ZZ K
      · change pullback.fst (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫
            (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) =
          pullback.snd (S2820E37ChartZMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K
        exact compat_false_true K
      · change pullback.fst (S2820E37ChartYMap K) (S2820E37ChartZMap K) ≫
            chartYNegGlued K =
          pullback.snd (S2820E37ChartYMap K) (S2820E37ChartZMap K) ≫
            (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K)
        exact compat_true_false K
      · change pullback.fst (S2820E37ChartYMap K) (S2820E37ChartYMap K) ≫
            chartYNegGlued K =
          pullback.snd (S2820E37ChartYMap K) (S2820E37ChartYMap K) ≫ chartYNegGlued K
        exact compat_YY K

/-- The global chart-alpha self-map of the fixed E37 projective scheme. -/
noncomputable def globalAlphaScheme :
    S2820E37ProjectiveScheme K ⟶ S2820E37ProjectiveScheme K :=
  globalAlpha K (globalAlphaCompat K)

#check globalAlphaCompat
#check globalAlphaScheme
#print axioms globalAlphaCompat
#print axioms globalAlphaScheme

end LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
end