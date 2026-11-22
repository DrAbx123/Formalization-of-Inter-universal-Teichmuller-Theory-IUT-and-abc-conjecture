/-
route 4.4 (L321-325), final assembly: the scheme-level morphism hPoly h : P^1 -> P^1
for a nonzero polynomial h : Q[lambda], together with its three chart descriptions.

The morphism is obtained by gluing THREE chart morphisms along the cover of P^1
   * piece 0 = the t-chart (coordinate t = 1/lambda), chart map t |-> h(t);
   * piece 1 = D(lambda) inside the lambda-chart, chart map t |-> lambda^{-d} hRev(lambda);
   * piece 2 = D(hRev) inside the lambda-chart, chart map lambda |-> lambda^d / hRev(lambda);
where hRev is the reverse polynomial.  The two lambda-chart pieces cover the lambda-chart
because (lambda, hRev) = 1, and piece 0 covers the t-chart.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyCoverActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyCoverAlgebraActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyEvalActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import tmp.sheaf.xif.paper.Mzk1SchemeOpensRangeInterfaceActual
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Tactic

/-! OWNER: henry; do not edit (part1/part2 subagents must stop). Final assembly `hPoly`/`hPoly_ι_*` is complete and watchdog-DONE, three axioms. Any rewrite must preserve every declaration in this file. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverAlgebraActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyEvalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual

variable (h : Polynomial ℚ)

/-! ## The index type of the three pieces -/

/-- The three pieces of the cover: the t-chart, D(lambda) and D(hRev). -/
inductive HIdx : Type
  | c0 : HIdx
  | c1 : HIdx
  | c2 : HIdx
  deriving DecidableEq

/-! ## The three pieces -/

/-- The underlying schemes of the three cover pieces. -/
noncomputable abbrev hPolyPieceFun (h : Polynomial ℚ) : HIdx → Scheme
  | HIdx.c0 => Spec (CommRingCat.of (Polynomial ℚ))
  | HIdx.c1 => Spec (CommRingCat.of (Localization.Away (Polynomial.X : Polynomial ℚ)))
  | HIdx.c2 => Spec (CommRingCat.of (Localization.Away (hRev h)))

/-- The three cover pieces as morphisms into P^1. -/
noncomputable abbrev hPolyPieceMap (h : Polynomial ℚ) : (i : HIdx) → hPolyPieceFun h i ⟶ projectiveLineGlued
  | HIdx.c0 => localChartInf
  | HIdx.c1 => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)))) ≫ localChart0
  | HIdx.c2 => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
      (Localization.Away (hRev h)))) ≫ localChart0

/-- Each piece is an open immersion. -/
instance hPolyPieceMap_isOpenImmersion (h : Polynomial ℚ) (i : HIdx) :
    IsOpenImmersion (hPolyPieceMap h i) := by
  cases i with
  | c0 => exact localChartInf_isOpenImmersion
  | c1 => exact IsOpenImmersion.comp _ _
  | c2 => exact IsOpenImmersion.comp _ _

/-- The chart morphisms, indexed by the three pieces. -/
noncomputable abbrev hPolyChartOf (h : Polynomial ℚ) :
    (i : HIdx) → hPolyPieceFun h i ⟶ projectiveLineGlued
  | HIdx.c0 => chartMorphismInf (R := Polynomial ℚ) h
  | HIdx.c1 => chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h)
  | HIdx.c2 => chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)

/-- The first chart morphism is the one of the hPoly file. -/
theorem hPolyChartOf_c0 (h : Polynomial ℚ) :
    hPolyChartOf h HIdx.c0 = hPolyChart0 h := rfl

/-! ## The range of the localization charts -/

/-- The open range of Spec of a localization map, as a basic open. -/
theorem opensRange_algebraMap_away {R : CommRingCat} (g : R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))).opensRange =
      (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum R)) :=
  Scheme.Hom.opensRange_localizationAway g

/-- The set-theoretic range of Spec of a localization map. -/
theorem range_algebraMap_away {R : CommRingCat} (g : R) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) =
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away g) g

/-- The two lambda-chart pieces cover the lambda-chart. -/
theorem chart0_cover (h : Polynomial ℚ) (hh : h ≠ 0) :
    (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of (Polynomial ℚ))
        (Localization.Away (Polynomial.X : Polynomial ℚ))))).opensRange ⊔
      (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of (Polynomial ℚ))
        (Localization.Away (hRev h))))).opensRange = ⊤ := by
  rw [opensRange_algebraMap_away (R := CommRingCat.of (Polynomial ℚ)) (Polynomial.X : Polynomial ℚ),
    opensRange_algebraMap_away (R := CommRingCat.of (Polynomial ℚ)) (hRev h)]
  exact basicOpen_X_sup_basicOpen_hRev h hh

/-! ## The cover -/

/-- The three pieces jointly cover P^1. -/
theorem hPolyCover_covers (h : Polynomial ℚ) (hh : h ≠ 0) :
    ∀ x : projectiveLineGlued, ∃ i y, (hPolyPieceMap h i) y = x := by
  intro x
  rcases localChart_jointly_surjective x with hx | hx
  · obtain ⟨y, rfl⟩ := hx
    have hys : y ∈ (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of (Polynomial ℚ))
          (Localization.Away (Polynomial.X : Polynomial ℚ))))).opensRange ⊔
        (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of (Polynomial ℚ))
          (Localization.Away (hRev h))))).opensRange := by
      rw [chart0_cover h hh]
      exact trivial
    simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union] at hys
    rcases hys with hys | hys
    · obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hys
      exact ⟨HIdx.c1, z, rfl⟩
    · obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hys
      exact ⟨HIdx.c2, z, rfl⟩
  · obtain ⟨y, rfl⟩ := hx
    exact ⟨HIdx.c0, y, rfl⟩

/-- The open cover of P^1 by the three chart pieces of hPoly. -/
noncomputable def hPolyCover (h : Polynomial ℚ) (hh : h ≠ 0) : Scheme.OpenCover.{0} projectiveLineGlued :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) HIdx (hPolyPieceFun h) (hPolyPieceMap h)
    (hPolyCover_covers h hh) (fun i => hPolyPieceMap_isOpenImmersion h i)

@[simp]
theorem hPolyCover_f (h : Polynomial ℚ) (hh : h ≠ 0) (i : (hPolyCover h hh).I₀) :
    (hPolyCover h hh).f i = hPolyPieceMap h i := rfl

/-- The images of the three pieces cover P^1. -/
theorem hPolyCover_iSup_opensRange (h : Polynomial ℚ) (hh : h ≠ 0) :
    (⨆ i : (hPolyCover h hh).I₀, ((hPolyCover h hh).f i).opensRange) = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, TopologicalSpace.Opens.coe_top,
    Set.mem_univ, iff_true]
  obtain ⟨i, y, hy⟩ := hPolyCover_covers h hh x
  exact ⟨i, Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩⟩


/-! ## Chart ring maps: substitution and the overlap transition -/

/-- The inversion of the overlap ring fixes the prime field. -/
theorem invAuto_C (r : ℚ) :
    invAuto (algebraMap ℚ OverlapRing r) = algebraMap ℚ OverlapRing r := by
  have h1 : algebraMap ℚ OverlapRing r =
      algebraMap (Polynomial ℚ) OverlapRing (Polynomial.C r) := by
    rw [Polynomial.C_eq_algebraMap,
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing r]
  rw [h1, invAuto, IsLocalization.Away.lift_eq]
  exact infMapR_C r

/-- Evaluation commutes with a ring map compatible with the base field. -/
theorem evalAt_map {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    (ρ : R →+* S) (hρ : ρ.comp (algebraMap ℚ R) = algebraMap ℚ S) (a : R) (p : Polynomial ℚ) :
    evalAt (ρ a) p = ρ (evalAt a p) := by
  have h1 : evalAt (R := R) a p = Polynomial.eval₂ (algebraMap ℚ R) a p := rfl
  have h2 : evalAt (R := S) (ρ a) p = Polynomial.eval₂ (algebraMap ℚ S) (ρ a) p := rfl
  rw [h1, h2, Polynomial.hom_eval₂ p (algebraMap ℚ R) ρ a, hρ]

/-- The evaluation maps compose along a ring map. -/
theorem evalAt_comp {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    (ρ : R →+* S) (hρ : ρ.comp (algebraMap ℚ R) = algebraMap ℚ S) (a : R) :
    evalAt (ρ a) = ρ.comp (evalAt a) :=
  RingHom.ext (fun p => evalAt_map ρ hρ a p)

/-- The inversion of the overlap ring sends the class of p to p at lambda inverse. -/
theorem invAuto_algebraMap_eq (p : Polynomial ℚ) :
    invAuto (algebraMap (Polynomial ℚ) OverlapRing p) =
      evalAt (R := OverlapRing) invLambda p := by
  have hinj : Function.Injective invAuto := by
    intro a b hab
    have ha := RingHom.congr_fun invAuto_comp_self a
    have hb := RingHom.congr_fun invAuto_comp_self b
    simp only [RingHom.comp_apply, RingHom.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  apply hinj
  have hL : invAuto (invAuto (algebraMap (Polynomial ℚ) OverlapRing p)) =
      algebraMap (Polynomial ℚ) OverlapRing p := by
    have := RingHom.congr_fun invAuto_comp_self (algebraMap (Polynomial ℚ) OverlapRing p)
    simpa using this
  have hR : invAuto (evalAt (R := OverlapRing) invLambda p) =
      algebraMap (Polynomial ℚ) OverlapRing p := by
    have hcomp := RingHom.congr_fun invAuto_comp_infMapR p
    simpa [evalAt, infMapR] using hcomp
  rw [hL, hR]

/-- The value of h at lambda inverse is hPolyT. -/
theorem evalAt_invLambda_h (h : Polynomial ℚ) (hh : h ≠ 0) :
    evalAt (R := OverlapRing) invLambda h = hPolyT h :=
  evalAt_invSelf_h h hh

/-- The overlap inclusion sends the variable to lambda inverse, giving hPolyT. -/
theorem hPolyT_eq (h : Polynomial ℚ) (hh : h ≠ 0) :
    (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) h = hPolyT h := by
  rw [RingHom.comp_apply, invAuto_algebraMap_eq, evalAt_invLambda_h h hh]

/-- The overlap inversion is compatible with the base field. -/
theorem invAuto_comp_algebraMap_base :
    (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)).comp
        (algebraMap ℚ (Polynomial ℚ)) = algebraMap ℚ OverlapRing := by
  ext r
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing r]
  exact invAuto_C r

/-- The t-chart morphism composed with a ring map. -/
theorem specMap_chartMorphismInf {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R]
    [Algebra ℚ S] (ρ : R →+* S) (hρ : ρ.comp (algebraMap ℚ R) = algebraMap ℚ S) (a : R) :
    Spec.map (CommRingCat.ofHom ρ) ≫ chartMorphismInf (R := R) a =
      chartMorphismInf (R := S) (ρ a) := by
  have hcomp : CommRingCat.ofHom (evalAt (R := R) a) ≫ CommRingCat.ofHom ρ =
      CommRingCat.ofHom (evalAt (R := S) (ρ a)) := by
    rw [← CommRingCat.ofHom_comp, ← evalAt_comp ρ hρ a]
  calc Spec.map (CommRingCat.ofHom ρ) ≫ chartMorphismInf (R := R) a
      = Spec.map (CommRingCat.ofHom ρ) ≫
          (Spec.map (CommRingCat.ofHom (evalAt (R := R) a)) ≫ localChartInf) := rfl
    _ = (Spec.map (CommRingCat.ofHom ρ) ≫
          Spec.map (CommRingCat.ofHom (evalAt (R := R) a))) ≫ localChartInf :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (evalAt (R := R) a) ≫ CommRingCat.ofHom ρ) ≫
          localChartInf := by rw [Spec.map_comp]
    _ = Spec.map (CommRingCat.ofHom (evalAt (R := S) (ρ a))) ≫ localChartInf := by rw [hcomp]
    _ = chartMorphismInf (R := S) (ρ a) := rfl

/-- The lambda-chart morphism composed with a ring map. -/
theorem specMap_chartMorphism0 {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R]
    [Algebra ℚ S] (ρ : R →+* S) (hρ : ρ.comp (algebraMap ℚ R) = algebraMap ℚ S) (a : R) :
    Spec.map (CommRingCat.ofHom ρ) ≫ chartMorphism0 (R := R) a =
      chartMorphism0 (R := S) (ρ a) := by
  have hcomp : CommRingCat.ofHom (evalAt (R := R) a) ≫ CommRingCat.ofHom ρ =
      CommRingCat.ofHom (evalAt (R := S) (ρ a)) := by
    rw [← CommRingCat.ofHom_comp, ← evalAt_comp ρ hρ a]
  calc Spec.map (CommRingCat.ofHom ρ) ≫ chartMorphism0 (R := R) a
      = Spec.map (CommRingCat.ofHom ρ) ≫
          (Spec.map (CommRingCat.ofHom (evalAt (R := R) a)) ≫ localChart0) := rfl
    _ = (Spec.map (CommRingCat.ofHom ρ) ≫
          Spec.map (CommRingCat.ofHom (evalAt (R := R) a))) ≫ localChart0 :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (evalAt (R := R) a) ≫ CommRingCat.ofHom ρ) ≫
          localChart0 := by rw [Spec.map_comp]
    _ = Spec.map (CommRingCat.ofHom (evalAt (R := S) (ρ a))) ≫ localChart0 := by rw [hcomp]
    _ = chartMorphism0 (R := S) (ρ a) := rfl

/-! ## Piece 1 is the overlap inside piece 0 -/

/-- Piece 1 equals the overlap inclusion followed by piece 0 (the P^1 chart transition). -/
theorem hPolyPiece1_eq (h : Polynomial ℚ) :
    hPolyPiece1 = overlapToChartInf ≫ hPolyPiece0 :=
  (p1GlueData.glue_condition (ULift.up false) (ULift.up true)).symm

/-- The t-chart map of h on the overlap is the t-chart map lambda^{-d} hRev(lambda). -/
theorem overlapToChartInf_chartMorphismInf (h : Polynomial ℚ) (hh : h ≠ 0) :
    overlapToChartInf ≫ chartMorphismInf (R := Polynomial ℚ) h =
      chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h) := by
  have hkey := specMap_chartMorphismInf (R := Polynomial ℚ)
    (S := Localization.Away (Polynomial.X : Polynomial ℚ))
    (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) invAuto_comp_algebraMap_base h
  rw [hPolyT_eq h hh] at hkey
  exact hkey

/-- The pullback square exhibiting the overlap as the intersection of pieces 0 and 1. -/
theorem isPullback_piece1_piece0 (h : Polynomial ℚ) :
    IsPullback overlapToChartInf (𝟙 overlapScheme) hPolyPiece0 hPolyPiece1 := by
  haveI : IsOpenImmersion hPolyPiece0 := isOpenImmersion_hPolyPiece0
  refine IsPullback.of_vert_isIso_mono ⟨?w⟩
  rw [Category.id_comp]
  exact (hPolyPiece1_eq h).symm

/-- Compatibility of the chart morphisms of pieces 0 and 1. -/
theorem compat_c0_c1 (h : Polynomial ℚ) (hh : h ≠ 0) :
    pullback.fst (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c1) ≫ hPolyChartOf h HIdx.c0 =
      pullback.snd (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c1) ≫
        hPolyChartOf h HIdx.c1 := by
  show pullback.fst hPolyPiece0 hPolyPiece1 ≫ chartMorphismInf (R := Polynomial ℚ) h =
    pullback.snd hPolyPiece0 hPolyPiece1 ≫
      chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h)
  have hpb := isPullback_piece1_piece0 h
  haveI : HasPullback hPolyPiece0 hPolyPiece1 := inferInstance
  let e := hpb.isoPullback
  have h1 : e.hom ≫ pullback.fst hPolyPiece0 hPolyPiece1 = overlapToChartInf :=
    IsPullback.isoPullback_hom_fst hpb
  have h2 : e.hom ≫ pullback.snd hPolyPiece0 hPolyPiece1 = 𝟙 overlapScheme :=
    IsPullback.isoPullback_hom_snd hpb
  haveI : Epi e.hom := inferInstance
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← Category.assoc, h1, h2, Category.id_comp]
  exact overlapToChartInf_chartMorphismInf h hh

/-! ## The affine overlap of the two lambda-chart pieces -/

/-- The intersection ring of the two lambda-chart pieces. -/
noncomputable abbrev Wring (h : Polynomial ℚ) : Type :=
  Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)

/-- The localization map from the lambda-chart ring localized at lambda. -/
noncomputable def toInt1 (h : Polynomial ℚ) :
    Localization.Away (Polynomial.X : Polynomial ℚ) →+* Wring h :=
  IsLocalization.Away.awayToAwayRight (Polynomial.X : Polynomial ℚ) (hRev h)

/-- The localization map from the lambda-chart ring localized at hRev. -/
noncomputable def toInt2 (h : Polynomial ℚ) :
    Localization.Away (hRev h) →+* Wring h :=
  IsLocalization.Away.awayToAwayLeft (hRev h) (Polynomial.X : Polynomial ℚ)

/-- A general composition formula for Spec maps. -/
theorem specMap_comp_eq {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map g ≫ Spec.map f = Spec.map (f ≫ g) :=
  (Spec.map_comp f g).symm

/-- The value of the first localization map on the base ring. -/
theorem toInt1_algebraMap (h : Polynomial ℚ) (a : Polynomial ℚ) :
    toInt1 h (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) a) =
      algebraMap (Polynomial ℚ) (Wring h) a :=
  IsLocalization.Away.awayToAwayRight_eq (Polynomial.X : Polynomial ℚ) (hRev h) a

/-- The value of the second localization map on the base ring. -/
theorem toInt2_algebraMap (h : Polynomial ℚ) (a : Polynomial ℚ) :
    toInt2 h (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) a) =
      algebraMap (Polynomial ℚ) (Wring h) a :=
  IsLocalization.Away.awayToAwayLeft_eq (hRev h) (Polynomial.X : Polynomial ℚ) a

/-- The first localization map commutes with the structure maps. -/
theorem toInt1_comp_algebraMap (h : Polynomial ℚ) :
    (toInt1 h).comp (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))) =
      algebraMap (Polynomial ℚ) (Wring h) :=
  RingHom.ext (fun a => toInt1_algebraMap h a)

/-- The second localization map commutes with the structure maps. -/
theorem toInt2_comp_algebraMap (h : Polynomial ℚ) :
    (toInt2 h).comp (algebraMap (Polynomial ℚ) (Localization.Away (hRev h))) =
      algebraMap (Polynomial ℚ) (Wring h) :=
  RingHom.ext (fun a => toInt2_algebraMap h a)

/-- The first localization map commutes with the base field. -/
theorem toInt1_base (h : Polynomial ℚ) :
    (toInt1 h).comp (algebraMap ℚ (Localization.Away (Polynomial.X : Polynomial ℚ))) =
      algebraMap ℚ (Wring h) := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)) r,
    IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (Wring h) r]
  exact toInt1_algebraMap h _

/-- The second localization map commutes with the base field. -/
theorem toInt2_base (h : Polynomial ℚ) :
    (toInt2 h).comp (algebraMap ℚ (Localization.Away (hRev h))) =
      algebraMap ℚ (Wring h) := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (Localization.Away (hRev h)) r,
    IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (Wring h) r]
  exact toInt2_algebraMap h _

/-- The first localization map sends the inverse of lambda to hRev times the inverse of
lambda hRev. -/
theorem toInt1_invSelf (h : Polynomial ℚ) :
    toInt1 h (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) =
      algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) := by
  have h1 : algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
      toInt1 h (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) = 1 := by
    rw [show algebraMap (Polynomial ℚ) (Wring h) Polynomial.X =
        toInt1 h (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
          Polynomial.X) from (toInt1_algebraMap h Polynomial.X).symm,
      ← map_mul, IsLocalization.Away.mul_invSelf (x := (Polynomial.X : Polynomial ℚ)), map_one]
  have h2 : algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
      (algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))) = 1 := by
    rw [← mul_assoc, ← map_mul,
      IsLocalization.Away.mul_invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))]
  calc toInt1 h (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ)))
      = 1 * toInt1 h (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) :=
        (one_mul _).symm
    _ = (algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
          (algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)))) *
          toInt1 h (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) := by
        rw [← h2]
    _ = (algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
          toInt1 h (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ)))) *
          (algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))) := by
        ring
    _ = 1 * (algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))) := by
        rw [h1]
    _ = algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) := one_mul _

/-- The second localization map sends the inverse of hRev to lambda times the inverse of
lambda hRev. -/
theorem toInt2_invSelf (h : Polynomial ℚ) :
    toInt2 h (IsLocalization.Away.invSelf (x := (hRev h))) =
      algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) := by
  have h1 : algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
      toInt2 h (IsLocalization.Away.invSelf (x := (hRev h))) = 1 := by
    rw [show algebraMap (Polynomial ℚ) (Wring h) (hRev h) =
        toInt2 h (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) (hRev h))
        from (toInt2_algebraMap h (hRev h)).symm,
      ← map_mul, IsLocalization.Away.mul_invSelf (x := (hRev h)), map_one]
  have h2 : algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
      (algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))) = 1 := by
    rw [← mul_assoc, ← map_mul, mul_comm (hRev h) (Polynomial.X),
      IsLocalization.Away.mul_invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))]
  calc toInt2 h (IsLocalization.Away.invSelf (x := (hRev h)))
      = 1 * toInt2 h (IsLocalization.Away.invSelf (x := (hRev h))) := (one_mul _).symm
    _ = (algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
          (algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)))) *
          toInt2 h (IsLocalization.Away.invSelf (x := (hRev h))) := by
        rw [← h2]
    _ = (algebraMap (Polynomial ℚ) (Wring h) (hRev h) *
          toInt2 h (IsLocalization.Away.invSelf (x := (hRev h)))) *
          (algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))) := by
        ring
    _ = 1 * (algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))) := by
        rw [h1]
    _ = algebraMap (Polynomial ℚ) (Wring h) Polynomial.X *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) := one_mul _

/-- The definition of the intersection t-coordinate. -/
theorem hPolyTOnIntersection_eq_aux (h : Polynomial ℚ) :
    hPolyTOnIntersection h =
      (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
        (hRev h)) ^ (h.natDegree + 1) *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) ^ h.natDegree :=
  rfl

/-- The definition of the intersection lambda-coordinate. -/
theorem hPolyLamOnIntersection_eq_aux (h : Polynomial ℚ) :
    hPolyLamOnIntersection h =
      (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
        Polynomial.X) ^ (h.natDegree + 1) *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) :=
  rfl

/-- The first chart coordinate on the intersection. -/
theorem toInt1_hPolyT (h : Polynomial ℚ) :
    toInt1 h (hPolyT h) = hPolyTOnIntersection h := by
  rw [hPolyT, hPolyTOnIntersection_eq_aux h, map_mul, map_pow, toInt1_invSelf h,
    toInt1_algebraMap h, mul_pow, pow_succ]
  ring

/-- The second chart coordinate on the intersection. -/
theorem toInt2_hPolyLam (h : Polynomial ℚ) :
    toInt2 h (hPolyLam h) = hPolyLamOnIntersection h := by
  rw [hPolyLam, hPolyLamOnIntersection_eq_aux h, map_mul, map_pow, toInt2_algebraMap h,
    toInt2_invSelf h, pow_succ]
  ring

/-! ## The factorization of the first localization map -/

/-- The two localizations of the lambda-chart ring at lambda hRev are canonically equal. -/
noncomputable def intAlgEquiv (h : Polynomial ℚ) :
    Wring h ≃ₐ[Polynomial ℚ]
      Localization.Away (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
        (hRev h)) :=
  IsLocalization.algEquiv (Submonoid.powers (Polynomial.X * hRev h : Polynomial ℚ)) _ _

/-- The canonical comparison of the two localizations composed with the first localization
map is the structure map. -/
theorem intAlgEquiv_comp_toInt1 (h : Polynomial ℚ) :
    (intAlgEquiv h).toRingEquiv.toRingHom.comp (toInt1 h) =
      algebraMap (Localization.Away (Polynomial.X : Polynomial ℚ))
        (Localization.Away (algebraMap (Polynomial ℚ)
          (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ)) ?_
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  rw [toInt1_algebraMap h a]
  refine (AlgEquiv.commutes (intAlgEquiv h) a).trans ?_
  exact (IsScalarTower.algebraMap_apply (Polynomial ℚ)
    (Localization.Away (Polynomial.X : Polynomial ℚ))
    (Localization.Away (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))) a).symm

/-- The canonical comparison of the two localizations is an isomorphism of commutative
rings. -/
theorem isIso_intAlgEquiv (h : Polynomial ℚ) :
    IsIso (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)) :=
  (RingEquiv.toCommRingCatIso ((intAlgEquiv h).toRingEquiv)).isIso_hom

/-- The structure map of the localization of the lambda-chart ring at hRev, factored through
the intersection ring. -/
theorem intStruct_eq (h : Polynomial ℚ) :
    Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (Polynomial.X : Polynomial ℚ))
        (Localization.Away (algebraMap (Polynomial ℚ)
          (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))))) =
      Spec.map (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (toInt1 h)) := by
  rw [specMap_comp_eq, ← CommRingCat.ofHom_comp, intAlgEquiv_comp_toInt1]

/-- The first localization map is an open immersion. -/
instance isOpenImmersion_toInt1 (h : Polynomial ℚ) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (toInt1 h))) := by
  haveI hi := isIso_intAlgEquiv h
  have hB : Spec.map (CommRingCat.ofHom (toInt1 h)) =
      (asIso (Spec.map (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)))).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (Polynomial.X : Polynomial ℚ))
          (Localization.Away (algebraMap (Polynomial ℚ)
            (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))))) := by
    rw [intStruct_eq h]
    exact (Iso.inv_hom_id_assoc
      (asIso (Spec.map (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)))) _).symm
  rw [hB]
  infer_instance

/-- The open range of the first localization map. -/
theorem a1_opensRange (h : Polynomial ℚ) :
    (Spec.map (CommRingCat.ofHom (toInt1 h))).opensRange =
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (Polynomial.X : Polynomial ℚ))
        (Localization.Away (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
          (hRev h)))))).opensRange := by
  haveI hi := isIso_intAlgEquiv h
  have hB : Spec.map (CommRingCat.ofHom (toInt1 h)) =
      (asIso (Spec.map (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)))).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (Polynomial.X : Polynomial ℚ))
          (Localization.Away (algebraMap (Polynomial ℚ)
            (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))))) := by
    rw [intStruct_eq h]
    exact (Iso.inv_hom_id_assoc
      (asIso (Spec.map (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)))) _).symm
  have hsurj : Set.range ⇑((asIso (Spec.map (CommRingCat.ofHom
      ((intAlgEquiv h).toRingEquiv.toRingHom)))).inv) = Set.univ :=
    Set.range_eq_univ.mpr (Scheme.homeoOfIso
      (asIso (Spec.map (CommRingCat.ofHom ((intAlgEquiv h).toRingEquiv.toRingHom)))).symm).surjective
  apply (opens_eq_iff_coe_eq _ _).mpr
  rw [opensRange_coe_eq_range, opensRange_coe_eq_range, hB, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, hsurj, Set.image_univ]

/-- The open range of the second localization map. -/
theorem u1_preimage_u2_opensRange (h : Polynomial ℚ) :
    (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X : Polynomial ℚ)))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
        (Localization.Away (hRev h))))).opensRange) =
      (Spec.map (CommRingCat.ofHom (toInt1 h))).opensRange := by
  rw [opensRange_algebraMap_away (R := CommRingCat.of (Polynomial ℚ)) (hRev h),
    AlgebraicGeometry.SpecMap_preimage_basicOpen]
  rw [show (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)))) (hRev h) =
      algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h)
    from rfl]
  exact ((opensRange_algebraMap_away (R := CommRingCat.of (Localization.Away (Polynomial.X : Polynomial ℚ)))
    (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))).symm).trans
    (a1_opensRange h).symm

/-- The pullback square: the intersection is the fibre product of the two lambda-chart
pieces over P^1. -/
theorem isPullback_p1_p2 (h : Polynomial ℚ) :
    IsPullback (Spec.map (CommRingCat.ofHom (toInt1 h)))
      (Spec.map (CommRingCat.ofHom (toInt2 h)))
      (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) := by
  have hflip : IsPullback (Spec.map (CommRingCat.ofHom (toInt2 h)))
      (Spec.map (CommRingCat.ofHom (toInt1 h)))
      (hPolyPieceMap h HIdx.c2) (hPolyPieceMap h HIdx.c1) := by
    haveI hi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (toInt1 h))) :=
      isOpenImmersion_toInt1 h
    haveI hi2 : IsOpenImmersion (hPolyPieceMap h HIdx.c2) :=
      hPolyPieceMap_isOpenImmersion h HIdx.c2
    refine IsOpenImmersion.isPullback (g := Spec.map (CommRingCat.ofHom (toInt2 h)))
      (iU := Spec.map (CommRingCat.ofHom (toInt1 h)))
      (iV := hPolyPieceMap h HIdx.c2) (f := hPolyPieceMap h HIdx.c1) ?_ ?_
    · rw [← Category.assoc, ← Category.assoc, specMap_comp_eq, specMap_comp_eq,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        toInt1_comp_algebraMap, toInt2_comp_algebraMap]
    · rw [Scheme.Hom.opensRange_comp, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
      exact u1_preimage_u2_opensRange h
  exact hflip.flip

/-- Compatibility of the chart morphisms of pieces 1 and 2. -/
theorem compat_c1_c2 (h : Polynomial ℚ) :
    pullback.fst (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) ≫ hPolyChartOf h HIdx.c1 =
      pullback.snd (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) ≫
        hPolyChartOf h HIdx.c2 := by
  show pullback.fst (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) ≫
      chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h) =
    pullback.snd (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) ≫
      chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)
  have hpb := isPullback_p1_p2 h
  haveI : HasPullback (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) := inferInstance
  let e := hpb.isoPullback
  have h1 : e.hom ≫ pullback.fst (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) =
      Spec.map (CommRingCat.ofHom (toInt1 h)) := IsPullback.isoPullback_hom_fst hpb
  have h2 : e.hom ≫ pullback.snd (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) =
      Spec.map (CommRingCat.ofHom (toInt2 h)) := IsPullback.isoPullback_hom_snd hpb
  haveI : Epi e.hom := inferInstance
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc, h1, h2, Category.id_comp]
  rw [specMap_chartMorphismInf (ρ := toInt1 h) (hρ := toInt1_base h) (a := hPolyT h),
    specMap_chartMorphism0 (ρ := toInt2 h) (hρ := toInt2_base h) (a := hPolyLam h),
    toInt1_hPolyT h, toInt2_hPolyLam h]
  exact hPoly_overlap_compat h


/-! ## The t-chart piece and the second lambda-chart piece -/

/-- The intersection, mapped to the t-chart through the overlap. -/
noncomputable def toChartInf (h : Polynomial ℚ) :
    Spec (CommRingCat.of (Wring h)) ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (toInt1 h)) ≫ overlapToChartInf

/-- The t-chart is an open immersion into P^1. -/
instance isOpenImmersion_localChartInf : IsOpenImmersion localChartInf :=
  localChartInf_isOpenImmersion

/-- The overlap inclusion into the t-chart is an open immersion. -/
instance isOpenImmersion_overlapToChartInf : IsOpenImmersion overlapToChartInf :=
  overlapToChartInf_isOpenImmersion

/-- The overlap inclusion into the lambda-chart is an open immersion. -/
instance isOpenImmersion_overlapToChart0 : IsOpenImmersion overlapToChart0 :=
  overlapToChart0_isOpenImmersion

/-- The intersection is an open immersion into the t-chart. -/
instance isOpenImmersion_toChartInf (h : Polynomial ℚ) : IsOpenImmersion (toChartInf h) :=
  IsOpenImmersion.comp _ _

/-- The gluing pullback square of the two charts of P^1. -/
theorem isPullback_charts :
    IsPullback overlapToChart0 overlapToChartInf localChart0 localChartInf :=
  IsOpenImmersion.isPullback (g := overlapToChart0) (iU := overlapToChartInf)
    (iV := localChart0) (f := localChartInf) localChart_overlap_condition
    localChartInf_preimage_localChart0

/-- The pullback square of the t-chart piece and the second lambda-chart piece. -/
theorem isPullback_p0_p2 (h : Polynomial ℚ) :
    IsPullback (toChartInf h) (Spec.map (CommRingCat.ofHom (toInt2 h)))
      (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) := by
  have hflip : IsPullback (Spec.map (CommRingCat.ofHom (toInt2 h))) (toChartInf h)
      (hPolyPieceMap h HIdx.c2) (hPolyPieceMap h HIdx.c0) := by
    haveI ha0 : IsOpenImmersion (toChartInf h) := isOpenImmersion_toChartInf h
    haveI hp2 : IsOpenImmersion (hPolyPieceMap h HIdx.c2) :=
      hPolyPieceMap_isOpenImmersion h HIdx.c2
    refine IsOpenImmersion.isPullback (g := Spec.map (CommRingCat.ofHom (toInt2 h)))
      (iU := toChartInf h) (iV := hPolyPieceMap h HIdx.c2)
      (f := hPolyPieceMap h HIdx.c0) ?_ ?_
    · -- the two composites into P^1 agree
      show Spec.map (CommRingCat.ofHom (toInt1 h)) ≫ overlapToChartInf ≫ localChartInf =
        Spec.map (CommRingCat.ofHom (toInt2 h)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
            (Localization.Away (hRev h)))) ≫ localChart0)
      rw [localChart_overlap_condition,
        show overlapToChart0 = Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
          (Localization.Away (Polynomial.X : Polynomial ℚ)))) from rfl]
      rw [← Category.assoc, specMap_comp_eq, ← CommRingCat.ofHom_comp, toInt1_comp_algebraMap]
      rw [← Category.assoc, specMap_comp_eq, ← CommRingCat.ofHom_comp, toInt2_comp_algebraMap]
    · -- the preimages agree
      unfold toChartInf
      have hstep1 : (hPolyPieceMap h HIdx.c2).opensRange =
          localChart0 ''ᵁ (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
            (Localization.Away (hRev h))))).opensRange :=
        Scheme.Hom.opensRange_comp _ _
      rw [hstep1]
      have hstep2 : hPolyPieceMap h HIdx.c0 ⁻¹ᵁ (localChart0 ''ᵁ (Spec.map (CommRingCat.ofHom
            (algebraMap (Polynomial ℚ) (Localization.Away (hRev h))))).opensRange)
          = localChartInf ⁻¹ᵁ (localChart0 ''ᵁ (Spec.map (CommRingCat.ofHom
            (algebraMap (Polynomial ℚ) (Localization.Away (hRev h))))).opensRange) := rfl
      rw [hstep2]
      rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (isPullback_charts)
        (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
          (Localization.Away (hRev h))))).opensRange]
      rw [show (overlapToChart0 ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
            (Localization.Away (hRev h))))).opensRange)
          = (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
              (Localization.Away (Polynomial.X : Polynomial ℚ)))) ⁻¹ᵁ
              (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
                (Localization.Away (hRev h))))).opensRange) from rfl,
        u1_preimage_u2_opensRange h, Scheme.Hom.opensRange_comp]
  exact hflip.flip

/-- Compatibility of the chart morphisms of pieces 0 and 2. -/
theorem compat_c0_c2 (h : Polynomial ℚ) (hh : h ≠ 0) :
    pullback.fst (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) ≫ hPolyChartOf h HIdx.c0 =
      pullback.snd (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) ≫
        hPolyChartOf h HIdx.c2 := by
  show pullback.fst (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) ≫
      chartMorphismInf (R := Polynomial ℚ) h =
    pullback.snd (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) ≫
      chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)
  have hpb := isPullback_p0_p2 h
  haveI : HasPullback (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) := inferInstance
  let e := hpb.isoPullback
  have h1 : e.hom ≫ pullback.fst (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) =
      toChartInf h := IsPullback.isoPullback_hom_fst hpb
  have h2 : e.hom ≫ pullback.snd (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) =
      Spec.map (CommRingCat.ofHom (toInt2 h)) := IsPullback.isoPullback_hom_snd hpb
  haveI : Epi e.hom := inferInstance
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc, h1, h2, Category.id_comp]
  unfold toChartInf
  rw [Category.assoc, overlapToChartInf_chartMorphismInf h hh,
    specMap_chartMorphismInf (ρ := toInt1 h) (hρ := toInt1_base h) (a := hPolyT h),
    specMap_chartMorphism0 (ρ := toInt2 h) (hρ := toInt2_base h) (a := hPolyLam h),
    toInt1_hPolyT h, toInt2_hPolyLam h]
  exact hPoly_overlap_compat h

/-! ## The glued morphism -/

/-- The three chart morphisms are compatible on the pairwise intersections. -/
theorem hPoly_compat_aux (h : Polynomial ℚ) (hh : h ≠ 0) :
    ∀ x y : HIdx, pullback.fst (hPolyPieceMap h x) (hPolyPieceMap h y) ≫ hPolyChartOf h x =
      pullback.snd (hPolyPieceMap h x) (hPolyPieceMap h y) ≫ hPolyChartOf h y := by
  intro x y
  cases x <;> cases y
  · have hfs : pullback.fst (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c0) =
        pullback.snd (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c0) := by
      rw [← cancel_mono (hPolyPieceMap h HIdx.c0), pullback.condition]
    rw [hfs]
  · exact compat_c0_c1 h hh
  · exact compat_c0_c2 h hh
  · -- c1, c0
    haveI : Epi (pullbackSymmetry (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c1)).hom :=
      inferInstance
    rw [← cancel_epi (pullbackSymmetry (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c1)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst]
    exact (compat_c0_c1 h hh).symm
  · have hfs : pullback.fst (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c1) =
        pullback.snd (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c1) := by
      rw [← cancel_mono (hPolyPieceMap h HIdx.c1), pullback.condition]
    rw [hfs]
  · exact compat_c1_c2 h
  · -- c2, c0
    haveI : Epi (pullbackSymmetry (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2)).hom :=
      inferInstance
    rw [← cancel_epi (pullbackSymmetry (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst]
    exact (compat_c0_c2 h hh).symm
  · -- c2, c1
    haveI : Epi (pullbackSymmetry (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2)).hom :=
      inferInstance
    rw [← cancel_epi (pullbackSymmetry (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst]
    exact (compat_c1_c2 h).symm
  · have hfs : pullback.fst (hPolyPieceMap h HIdx.c2) (hPolyPieceMap h HIdx.c2) =
        pullback.snd (hPolyPieceMap h HIdx.c2) (hPolyPieceMap h HIdx.c2) := by
      rw [← cancel_mono (hPolyPieceMap h HIdx.c2), pullback.condition]
    rw [hfs]

/-- The three chart morphisms are compatible on the pairwise intersections of the cover. -/
theorem hPoly_compat (h : Polynomial ℚ) (hh : h ≠ 0) :
    ∀ x y : (hPolyCover h hh).I₀,
      pullback.fst ((hPolyCover h hh).f x) ((hPolyCover h hh).f y) ≫ hPolyChartOf h x =
        pullback.snd ((hPolyCover h hh).f x) ((hPolyCover h hh).f y) ≫ hPolyChartOf h y :=
  hPoly_compat_aux h hh

/-- The scheme-level morphism hPoly : P^1 ⟶ P^1 attached to a nonzero polynomial h. -/
noncomputable def hPoly (h : Polynomial ℚ) (hh : h ≠ 0) :
    projectiveLineGlued ⟶ projectiveLineGlued :=
  (hPolyCover h hh).glueMorphisms (hPolyChartOf h) (hPoly_compat h hh)

/-- The t-chart piece of hPoly. -/
theorem hPoly_ι_c0 (h : Polynomial ℚ) (hh : h ≠ 0) :
    (hPolyCover h hh).f HIdx.c0 ≫ hPoly h hh = hPolyChartOf h HIdx.c0 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := hPolyCover h hh) (f := hPolyChartOf h)
    (hf := hPoly_compat h hh) HIdx.c0

/-- The D(lambda) piece of hPoly. -/
theorem hPoly_ι_c1 (h : Polynomial ℚ) (hh : h ≠ 0) :
    (hPolyCover h hh).f HIdx.c1 ≫ hPoly h hh = hPolyChartOf h HIdx.c1 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := hPolyCover h hh) (f := hPolyChartOf h)
    (hf := hPoly_compat h hh) HIdx.c1

/-- The D(hRev) piece of hPoly. -/
theorem hPoly_ι_c2 (h : Polynomial ℚ) (hh : h ≠ 0) :
    (hPolyCover h hh).f HIdx.c2 ≫ hPoly h hh = hPolyChartOf h HIdx.c2 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := hPolyCover h hh) (f := hPolyChartOf h)
    (hf := hPoly_compat h hh) HIdx.c2

#print axioms hPolyPieceFun
#print axioms hPolyPieceMap
#print axioms hPolyPieceMap_isOpenImmersion
#print axioms hPolyChartOf
#print axioms opensRange_algebraMap_away
#print axioms range_algebraMap_away
#print axioms chart0_cover
#print axioms hPolyCover_covers
#print axioms hPolyCover
#print axioms hPolyCover_iSup_opensRange
#print axioms evalAt_map
#print axioms evalAt_comp
#print axioms invAuto_C
#print axioms invAuto_algebraMap_eq
#print axioms evalAt_invLambda_h
#print axioms hPolyT_eq
#print axioms specMap_chartMorphismInf
#print axioms specMap_chartMorphism0
#print axioms hPolyPiece1_eq
#print axioms overlapToChartInf_chartMorphismInf
#print axioms isPullback_piece1_piece0
#print axioms compat_c0_c1
#print axioms toInt1_hPolyT
#print axioms toInt2_hPolyLam
#print axioms isPullback_p1_p2
#print axioms compat_c1_c2
#print axioms isPullback_p0_p2
#print axioms compat_c0_c2
#print axioms hPoly_compat_aux
#print axioms hPoly_compat
#print axioms hPoly
#print axioms hPoly_ι_c0
#print axioms hPoly_ι_c1
#print axioms hPoly_ι_c2

#print axioms hPolyCover_f
#print axioms hPolyChartOf_c0
#print axioms Wring
#print axioms toInt1
#print axioms toInt2
#print axioms specMap_comp_eq
#print axioms toInt1_algebraMap
#print axioms toInt2_algebraMap
#print axioms toInt1_comp_algebraMap
#print axioms toInt2_comp_algebraMap
#print axioms toInt1_base
#print axioms toInt2_base
#print axioms toInt1_invSelf
#print axioms toInt2_invSelf
#print axioms hPolyTOnIntersection_eq_aux
#print axioms hPolyLamOnIntersection_eq_aux
#print axioms intAlgEquiv
#print axioms intAlgEquiv_comp_toInt1
#print axioms isIso_intAlgEquiv
#print axioms intStruct_eq
#print axioms isOpenImmersion_toInt1
#print axioms a1_opensRange
#print axioms u1_preimage_u2_opensRange
#print axioms isPullback_charts
#print axioms isOpenImmersion_localChartInf
#print axioms isOpenImmersion_overlapToChartInf
#print axioms isOpenImmersion_overlapToChart0
#print axioms toChartInf
#print axioms isOpenImmersion_toChartInf
#print axioms hPolyPiece1_eq

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
