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


end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverAlgebraActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyEvalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual

/-! ## The intersection of the pieces 1 and 2

The intersection of the ranges of the pieces is the localization of the D(hRev) piece at
the image of lambda.  On this ring the inclusion into piece 2 is an honest localization map
(hence an open immersion with computable range), while the inclusion into piece 1 is the
induced map from D(lambda), and the inclusion into the t-chart is evaluation at the
t-coordinate lambda^{-1}.  Both mixed compatibility squares are then instances of
IsOpenImmersion.isPullback, and the two chart morphisms agree on the intersection by the
chart transition chartMorphism_transition applied to the unit lambda^d / hRev. -/

/-- The ring of the intersection of the D(hRev) piece with the lambda-chart: the
localization of D(hRev) at the image of lambda. -/
abbrev hPolyIntRing (h : Polynomial ℚ) : Type :=
  Localization.Away (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) (Polynomial.X))

/-- The intersection scheme of the pieces 1 and 2 (also the intersection of 0 and 2). -/
noncomputable abbrev hPolyIntScheme (h : Polynomial ℚ) : Scheme :=
  Spec (CommRingCat.of (hPolyIntRing h))

/-- In the intersection ring, lambda is a unit. -/
theorem isUnit_hPolyIntRing_X (h : Polynomial ℚ) :
    IsUnit (algebraMap (Polynomial ℚ) (hPolyIntRing h) (Polynomial.X)) :=
  IsLocalization.Away.isUnit_of_dvd (S := hPolyIntRing h) (x := hRev h * Polynomial.X)
    (r := Polynomial.X) (dvd_mul_left _ _)

/-- In the intersection ring, hRev is a unit. -/
theorem isUnit_hPolyIntRing_hRev (h : Polynomial ℚ) :
    IsUnit (algebraMap (Polynomial ℚ) (hPolyIntRing h) (hRev h)) :=
  IsLocalization.Away.isUnit_of_dvd (S := hPolyIntRing h) (x := hRev h * Polynomial.X)
    (r := hRev h) (dvd_mul_right _ _)

/-- Uniqueness of a right inverse in a commutative ring. -/
theorem eq_of_mul_eq_one_left {A : Type} [CommRing A] {a b c : A} (hb : a * b = 1) (hc : a * c = 1) :
    b = c := by
  calc b = b * 1 := (mul_one b).symm
    _ = b * (a * c) := by rw [hc]
    _ = b * a * c := by rw [mul_assoc]
    _ = 1 * c := by rw [mul_comm b a, hb]
    _ = c := one_mul c

/-- The unit lambda of the intersection ring. -/
noncomputable def hPolyIntLamUnit (h : Polynomial ℚ) : (hPolyIntRing h)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := hPolyIntRing h)
    (x := algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X)).unit

theorem hPolyIntLamUnit_val (h : Polynomial ℚ) :
    ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) =
      algebraMap (Localization.Away (hRev h)) (hPolyIntRing h)
        (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) :=
  IsUnit.unit_spec _

/-- The value of the lambda-unit is the image of lambda. -/
theorem hPolyIntLamUnit_val_eq (h : Polynomial ℚ) :
    ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) =
      algebraMap (Polynomial ℚ) (hPolyIntRing h) Polynomial.X := by
  rw [hPolyIntLamUnit_val h]
  exact (IsScalarTower.algebraMap_apply (Polynomial ℚ) (Localization.Away (hRev h))
    (hPolyIntRing h) Polynomial.X).symm

/-- The unit hRev of the intersection ring. -/
noncomputable def hPolyIntHUnit (h : Polynomial ℚ) : (hPolyIntRing h)ˣ :=
  (isUnit_hPolyIntRing_hRev h).unit

theorem hPolyIntHUnit_val (h : Polynomial ℚ) :
    ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) =
      algebraMap (Polynomial ℚ) (hPolyIntRing h) (hRev h) :=
  IsUnit.unit_spec _

/-- The t-coordinate lambda^{-1} on the intersection. -/
noncomputable def hPolyIntTau (h : Polynomial ℚ) : hPolyIntRing h :=
  (((hPolyIntLamUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h)

/-- The t-coordinate is invSelf of the localized element. -/
theorem hPolyIntTau_eq_invSelf (h : Polynomial ℚ) :
    hPolyIntTau h = IsLocalization.Away.invSelf (S := hPolyIntRing h)
      (x := algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) := by
  refine eq_of_mul_eq_one_left (a := algebraMap (Localization.Away (hRev h))
    (hPolyIntRing h) (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X)) ?_ ?_
  · rw [← hPolyIntLamUnit_val h]
    exact Units.mul_inv _
  · exact IsLocalization.Away.mul_invSelf (S := hPolyIntRing h)
      (x := algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X)

/-- The unit of the intersection with value lambda^d / hRev and inverse t^d * hRev. -/
noncomputable def hPolyIntUnit (h : Polynomial ℚ) : (hPolyIntRing h)ˣ where
  val := ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) ^ h.natDegree *
    (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h)
  inv := hPolyIntTau h ^ h.natDegree *
    ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h)
  val_inv := by
    have h1 : ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) * hPolyIntTau h = 1 :=
      Units.mul_inv _
    have h2 : (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
        ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) = 1 :=
      Units.inv_mul _
    calc ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) ^ h.natDegree *
          (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
          (hPolyIntTau h ^ h.natDegree *
            ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h))
        = (((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
            hPolyIntTau h) ^ h.natDegree *
          ((((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
            ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h)) := by ring
      _ = 1 := by rw [h1, h2, one_pow, one_mul]
  inv_val := by
    have h1 : ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) * hPolyIntTau h = 1 :=
      Units.mul_inv _
    have h2 : (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
        ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) = 1 :=
      Units.inv_mul _
    calc hPolyIntTau h ^ h.natDegree *
          ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
          (((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) ^ h.natDegree *
            (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h))
        = (((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
            hPolyIntTau h) ^ h.natDegree *
          ((((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) *
            ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h)) := by ring
      _ = 1 := by rw [h1, h2, one_pow, one_mul]

theorem hPolyIntUnit_val (h : Polynomial ℚ) :
    ((hPolyIntUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) =
      ((hPolyIntLamUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) ^ h.natDegree *
        (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) := rfl

theorem hPolyIntUnit_inv_val (h : Polynomial ℚ) :
    (((hPolyIntUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) =
      hPolyIntTau h ^ h.natDegree *
        ((hPolyIntHUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) := rfl

/-! ## The inclusions of the intersection into the three pieces -/

/-- The intersection sits inside piece 2 (D(hRev)) by localization. -/
noncomputable def hPolyIntToChart2 (h : Polynomial ℚ) :
    hPolyIntScheme h ⟶ hPolyPieceFun h HIdx.c2 :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (hRev h)) (hPolyIntRing h)))

instance hPolyIntToChart2_isOpenImmersion (h : Polynomial ℚ) :
    IsOpenImmersion (hPolyIntToChart2 h) := by
  unfold hPolyIntToChart2
  infer_instance

/-- The image of the intersection in piece 2. -/
theorem hPolyIntToChart2_opensRange (h : Polynomial ℚ) :
    (hPolyIntToChart2 h).opensRange =
      (PrimeSpectrum.basicOpen
        (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) :
        TopologicalSpace.Opens (PrimeSpectrum (Localization.Away (hRev h)))) := by
  unfold hPolyIntToChart2
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Localization.Away (hRev h)))
    (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X)

/-- The base-field compatibility of the inclusion into piece 2. -/
theorem hPolyIntToChart2_comp_base (h : Polynomial ℚ) :
    (algebraMap (Localization.Away (hRev h)) (hPolyIntRing h)).comp
        (algebraMap ℚ (Localization.Away (hRev h))) = algebraMap ℚ (hPolyIntRing h) := by
  ext r
  rw [RingHom.comp_apply]
  exact (IsScalarTower.algebraMap_apply ℚ (Localization.Away (hRev h)) (hPolyIntRing h) r).symm

/-- The map from the D(lambda) piece to the intersection. -/
noncomputable def hPolyIntFromChart1 (h : Polynomial ℚ) :
    Localization.Away (Polynomial.X : Polynomial ℚ) →+* hPolyIntRing h :=
  IsLocalization.Away.lift (S := Localization.Away (Polynomial.X : Polynomial ℚ))
    (x := (Polynomial.X : Polynomial ℚ))
    (g := algebraMap (Polynomial ℚ) (hPolyIntRing h)) (isUnit_hPolyIntRing_X h)

theorem hPolyIntFromChart1_comp (h : Polynomial ℚ) :
    (hPolyIntFromChart1 h).comp
        (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))) =
      algebraMap (Polynomial ℚ) (hPolyIntRing h) :=
  IsLocalization.Away.lift_comp (S := Localization.Away (Polynomial.X : Polynomial ℚ))
    (x := (Polynomial.X : Polynomial ℚ)) (g := algebraMap (Polynomial ℚ) (hPolyIntRing h))
    (isUnit_hPolyIntRing_X h)

theorem hPolyIntFromChart1_algebraMap (h : Polynomial ℚ) (a : Polynomial ℚ) :
    hPolyIntFromChart1 h
        (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) a) =
      algebraMap (Polynomial ℚ) (hPolyIntRing h) a :=
  RingHom.congr_fun (hPolyIntFromChart1_comp h) a

theorem hPolyIntFromChart1_comp_base (h : Polynomial ℚ) :
    (hPolyIntFromChart1 h).comp
        (algebraMap ℚ (Localization.Away (Polynomial.X : Polynomial ℚ))) =
      algebraMap ℚ (hPolyIntRing h) := by
  ext r
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)) r,
    ← RingHom.comp_apply, hPolyIntFromChart1_comp h,
    (IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (hPolyIntRing h) r).symm]

/-- The intersection sits inside piece 1 (D(lambda)) through the induced map. -/
noncomputable def hPolyIntToChart1 (h : Polynomial ℚ) :
    hPolyIntScheme h ⟶ hPolyPieceFun h HIdx.c1 :=
  Spec.map (CommRingCat.ofHom (hPolyIntFromChart1 h))

/-- The image of invSelf of lambda under the map from piece 1 is tau. -/
theorem hPolyIntFromChart1_invSelf_X (h : Polynomial ℚ) :
    hPolyIntFromChart1 h
        (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial ℚ))
          (x := (Polynomial.X : Polynomial ℚ))) = hPolyIntTau h := by
  refine eq_of_mul_eq_one_left (a := algebraMap (Polynomial ℚ) (hPolyIntRing h) Polynomial.X) ?_ ?_
  · rw [← hPolyIntFromChart1_algebraMap h Polynomial.X, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  · rw [← hPolyIntLamUnit_val_eq h]
    exact Units.mul_inv _

/-- The image of invSelf of hRev under the inclusion into piece 2. -/
theorem algebraMap_invSelf_hRev_int (h : Polynomial ℚ) :
    algebraMap (Localization.Away (hRev h)) (hPolyIntRing h)
        (IsLocalization.Away.invSelf (S := Localization.Away (hRev h)) (x := hRev h)) =
      (((hPolyIntHUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) := by
  refine eq_of_mul_eq_one_left
    (a := algebraMap (Polynomial ℚ) (hPolyIntRing h) (hRev h)) ?_ ?_
  · rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) (Localization.Away (hRev h))
      (hPolyIntRing h) (hRev h), ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  · rw [← hPolyIntHUnit_val h]
    exact Units.mul_inv _

/-! ## The chart morphisms agree on the intersection -/

/-- On the intersection, the chart map of piece 1 lands on tau^d * hRev. -/
theorem hPolyIntFromChart1_hPolyT (h : Polynomial ℚ) :
    hPolyIntFromChart1 h (hPolyT h) =
      (((hPolyIntUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) := by
  simp only [hPolyT, map_mul, map_pow]
  rw [hPolyIntFromChart1_invSelf_X h,
    hPolyIntFromChart1_algebraMap h (hRev h), hPolyIntUnit_inv_val h,
    hPolyIntHUnit_val h]

/-- On the intersection, the chart map of piece 2 lands on lambda^d / hRev. -/
theorem hPolyInt_algMap_hPolyLam (h : Polynomial ℚ) :
    algebraMap (Localization.Away (hRev h)) (hPolyIntRing h) (hPolyLam h) =
      ((hPolyIntUnit h : (hPolyIntRing h)ˣ) : hPolyIntRing h) := by
  simp only [hPolyLam, map_mul, map_pow]
  rw [algebraMap_invSelf_hRev_int h, hPolyIntUnit_val h, hPolyIntLamUnit_val h]

/-- The two chart morphisms of hPoly agree on the intersection. -/
theorem hPolyInt_transport (h : Polynomial ℚ) :
    chartMorphismInf (R := hPolyIntRing h) (hPolyIntFromChart1 h (hPolyT h)) =
      chartMorphism0 (R := hPolyIntRing h)
        (algebraMap (Localization.Away (hRev h)) (hPolyIntRing h) (hPolyLam h)) := by
  rw [hPolyIntFromChart1_hPolyT h, hPolyInt_algMap_hPolyLam h]
  exact (chartMorphism_transition (R := hPolyIntRing h) (hPolyIntUnit h)).symm

/-- The composite of the inclusion into piece 2 with the chart map of piece 2. -/
theorem hPolyIntToChart2_chartMorphism0 (h : Polynomial ℚ) (a : Localization.Away (hRev h)) :
    hPolyIntToChart2 h ≫ chartMorphism0 (R := Localization.Away (hRev h)) a =
      chartMorphism0 (R := hPolyIntRing h)
        (algebraMap (Localization.Away (hRev h)) (hPolyIntRing h) a) :=
  specMap_chartMorphism0 (R := Localization.Away (hRev h)) (S := hPolyIntRing h)
    (algebraMap (Localization.Away (hRev h)) (hPolyIntRing h)) (hPolyIntToChart2_comp_base h) a

/-- The composite of the inclusion into piece 1 with the chart map of piece 1. -/
theorem hPolyIntToChart1_chartMorphismInf (h : Polynomial ℚ)
    (a : Localization.Away (Polynomial.X : Polynomial ℚ)) :
    hPolyIntToChart1 h ≫ chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) a =
      chartMorphismInf (R := hPolyIntRing h) (hPolyIntFromChart1 h a) :=
  specMap_chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ))
    (S := hPolyIntRing h) (hPolyIntFromChart1 h) (hPolyIntFromChart1_comp_base h) a

/-- evalAt is compatible with the base field. -/
theorem evalAt_comp_algebraMap_base {R : Type} [CommRing R] [Algebra ℚ R] (a : R) :
    (evalAt (R := R) a).comp (algebraMap ℚ (Polynomial ℚ)) = algebraMap ℚ R := by
  ext r
  simpa using evalAt_C (R := R) a r

/-- The intersection sits in the t-chart with coordinate tau. -/
noncomputable def hPolyIntToChart0 (h : Polynomial ℚ) :
    hPolyIntScheme h ⟶ hPolyPieceFun h HIdx.c0 :=
  Spec.map (CommRingCat.ofHom (evalAt (R := hPolyIntRing h) (hPolyIntTau h)))

theorem hPolyIntToChart0_piece0 (h : Polynomial ℚ) :
    hPolyIntToChart0 h ≫ hPolyPieceMap h HIdx.c0 =
      chartMorphismInf (R := hPolyIntRing h) (hPolyIntTau h) := rfl

/-- The composite of the inclusion into the t-chart with the chart map of piece 0. -/
theorem hPolyIntToChart0_chartMorphismInf (h : Polynomial ℚ) :
    hPolyIntToChart0 h ≫ chartMorphismInf (R := Polynomial ℚ) h =
      chartMorphismInf (R := hPolyIntRing h)
        (evalAt (R := hPolyIntRing h) (hPolyIntTau h) h) :=
  specMap_chartMorphismInf (R := Polynomial ℚ) (S := hPolyIntRing h)
    (evalAt (R := hPolyIntRing h) (hPolyIntTau h))
    (evalAt_comp_algebraMap_base (hPolyIntTau h)) h

/-- The t-chart map of h at the intersection is tau^d * hRev. -/
theorem evalAt_tau_h (h : Polynomial ℚ) (hh : h ≠ 0) :
    evalAt (R := hPolyIntRing h) (hPolyIntTau h) h =
      (((hPolyIntUnit h)⁻¹ : (hPolyIntRing h)ˣ) : hPolyIntRing h) := by
  rw [← hPolyIntFromChart1_invSelf_X h,
    evalAt_comp (hPolyIntFromChart1 h) (hPolyIntFromChart1_comp_base h)
      (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ)))]
  rw [RingHom.comp_apply, evalAt_invSelf_h h hh]
  simp only [map_mul, map_pow]
  rw [hPolyIntFromChart1_invSelf_X h,
    hPolyIntFromChart1_algebraMap h (hRev h), hPolyIntUnit_inv_val h,
    hPolyIntHUnit_val h]

/-- evalAt at the image of lambda is the structure map. -/
theorem evalAt_algebraMap_X_int (h : Polynomial ℚ) :
    evalAt (R := hPolyIntRing h)
        (algebraMap (Polynomial ℚ) (hPolyIntRing h) Polynomial.X) =
      algebraMap (Polynomial ℚ) (hPolyIntRing h) := by
  apply RingHom.ext
  intro p
  show Polynomial.aeval (algebraMap (Polynomial ℚ) (hPolyIntRing h) Polynomial.X) p =
    algebraMap (Polynomial ℚ) (hPolyIntRing h) p
  rw [Polynomial.aeval_def]
  simpa using Polynomial.eval₂_algebraMap_X (A := hPolyIntRing h) p
    (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) (hPolyIntRing h))

/-! ## The two mixed compatibility squares are pullbacks -/

/-- The chart inclusion of D(lambda) in the lambda-chart. -/
noncomputable def hPolyPiece1Chart :
    Spec (CommRingCat.of (Localization.Away (Polynomial.X : Polynomial ℚ))) ⟶ chart0Scheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))))

/-- The chart inclusion of D(hRev) in the lambda-chart. -/
noncomputable def hPolyPiece2Chart (h : Polynomial ℚ) :
    Spec (CommRingCat.of (Localization.Away (hRev h))) ⟶ chart0Scheme :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (Localization.Away (hRev h))))

instance hPolyPiece1Chart_isOpenImmersion : IsOpenImmersion hPolyPiece1Chart := by
  unfold hPolyPiece1Chart
  infer_instance

instance hPolyPiece2Chart_isOpenImmersion (h : Polynomial ℚ) : IsOpenImmersion (hPolyPiece2Chart h) := by
  unfold hPolyPiece2Chart
  infer_instance

/-- Preimage of a basic open along the map of spectra induced by a ring map. -/
theorem specMap_preimage_basicOpen {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (ρ r) : TopologicalSpace.Opens (PrimeSpectrum S)) :=
  PrimeSpectrum.comap_basicOpen ρ r

theorem hPolyPiece1Chart_opensRange :
    hPolyPiece1Chart.opensRange =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) :
        TopologicalSpace.Opens (PrimeSpectrum (Polynomial ℚ))) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Polynomial ℚ)) Polynomial.X

theorem hPolyPiece2Chart_opensRange (h : Polynomial ℚ) :
    (hPolyPiece2Chart h).opensRange =
      (PrimeSpectrum.basicOpen (hRev h) :
        TopologicalSpace.Opens (PrimeSpectrum (Polynomial ℚ))) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Polynomial ℚ)) (hRev h)

/-- The preimage of the range of piece 1 under the inclusion of piece 2 is the range of
the intersection in piece 2. -/
theorem hPolyInt_preimage_piece1 (h : Polynomial ℚ) :
    (hPolyPieceMap h HIdx.c2) ⁻¹ᵁ (hPolyPieceMap h HIdx.c1).opensRange =
      (hPolyIntToChart2 h).opensRange := by
  show (hPolyPiece2 h) ⁻¹ᵁ hPolyPiece1.opensRange = _
  rw [hPolyIntToChart2_opensRange h]
  calc (hPolyPiece2 h) ⁻¹ᵁ hPolyPiece1.opensRange
      = (hPolyPiece2Chart h) ⁻¹ᵁ hPolyPiece1Chart.opensRange := by
        rw [show hPolyPiece1.opensRange = localChart0 ''ᵁ hPolyPiece1Chart.opensRange from
          Scheme.Hom.opensRange_comp hPolyPiece1Chart localChart0]
        show (hPolyPiece2Chart h ≫ localChart0) ⁻¹ᵁ
            (localChart0 ''ᵁ hPolyPiece1Chart.opensRange) = _
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
    _ = (PrimeSpectrum.basicOpen
          (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) :
          TopologicalSpace.Opens (PrimeSpectrum (Localization.Away (hRev h)))) := by
        rw [hPolyPiece1Chart_opensRange]
        exact specMap_preimage_basicOpen _ _

/-- The preimage of the range of piece 0 under the inclusion of piece 2 is the range of
the intersection in piece 2. -/
theorem hPolyInt_preimage_piece0 (h : Polynomial ℚ) :
    (hPolyPieceMap h HIdx.c2) ⁻¹ᵁ (hPolyPieceMap h HIdx.c0).opensRange =
      (hPolyIntToChart2 h).opensRange := by
  show (hPolyPiece2 h) ⁻¹ᵁ hPolyPiece0.opensRange = _
  rw [hPolyIntToChart2_opensRange h]
  calc (hPolyPiece2 h) ⁻¹ᵁ hPolyPiece0.opensRange
      = (hPolyPiece2Chart h) ⁻¹ᵁ overlapToChart0.opensRange := by
        show (hPolyPiece2Chart h ≫ localChart0) ⁻¹ᵁ localChartInf.opensRange = _
        rw [Scheme.Hom.comp_preimage, localChart0_preimage_localChartInf]
    _ = (PrimeSpectrum.basicOpen
          (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) :
          TopologicalSpace.Opens (PrimeSpectrum (Localization.Away (hRev h)))) := by
        rw [show overlapToChart0.opensRange =
          (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) :
            TopologicalSpace.Opens (PrimeSpectrum (Polynomial ℚ))) from
          Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Polynomial ℚ)) Polynomial.X]
        exact specMap_preimage_basicOpen _ _

/-- The composite of the inclusion into piece 2 with piece 2 is the localization map. -/
theorem hPolyIntToChart2_piece2 (h : Polynomial ℚ) :
    hPolyIntToChart2 h ≫ hPolyPieceMap h HIdx.c2 =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (hPolyIntRing h))) ≫ localChart0 := by
  show hPolyIntToChart2 h ≫ hPolyPiece2 h = _
  unfold hPolyIntToChart2 hPolyPiece2
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq (Polynomial ℚ) (Localization.Away (hRev h)) (hPolyIntRing h)]

/-- The composite of the inclusion into piece 1 with piece 1 is the localization map. -/
theorem hPolyIntToChart1_piece1 (h : Polynomial ℚ) :
    hPolyIntToChart1 h ≫ hPolyPieceMap h HIdx.c1 =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (hPolyIntRing h))) ≫ localChart0 := by
  show hPolyIntToChart1 h ≫ hPolyPiece1 = _
  unfold hPolyIntToChart1 hPolyPiece1 hPolyIntFromChart1
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    IsLocalization.Away.lift_comp (S := Localization.Away (Polynomial.X : Polynomial ℚ))
      (x := (Polynomial.X : Polynomial ℚ)) (g := algebraMap (Polynomial ℚ) (hPolyIntRing h))
      (isUnit_hPolyIntRing_X h)]

/-- Commutativity of the square of the pieces 1 and 2. -/
theorem hPolyInt_square1 (h : Polynomial ℚ) :
    hPolyIntToChart2 h ≫ hPolyPieceMap h HIdx.c2 =
      hPolyIntToChart1 h ≫ hPolyPieceMap h HIdx.c1 :=
  (hPolyIntToChart2_piece2 h).trans (hPolyIntToChart1_piece1 h).symm

/-- Commutativity of the square of the pieces 0 and 2. -/
theorem hPolyInt_square0 (h : Polynomial ℚ) :
    hPolyIntToChart2 h ≫ hPolyPieceMap h HIdx.c2 =
      hPolyIntToChart0 h ≫ hPolyPieceMap h HIdx.c0 := by
  rw [hPolyIntToChart2_piece2 h, hPolyIntToChart0_piece0 h]
  have hC : chartMorphism0 (R := hPolyIntRing h)
      (algebraMap (Polynomial ℚ) (hPolyIntRing h) Polynomial.X) =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (hPolyIntRing h))) ≫ localChart0 := by
    unfold chartMorphism0
    rw [evalAt_algebraMap_X_int h]
  rw [← hC, ← hPolyIntLamUnit_val_eq h]
  exact chartMorphism_transition (R := hPolyIntRing h) (hPolyIntLamUnit h)

/-! ## The mixed compatibilities of the chart morphisms -/

/-- Compatibility of the chart morphisms of pieces 1 and 2. -/
theorem compat_c1_c2 (h : Polynomial ℚ) (hh : h ≠ 0) :
    pullback.fst (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) ≫ hPolyChartOf h HIdx.c1 =
      pullback.snd (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2) ≫
        hPolyChartOf h HIdx.c2 := by
  show pullback.fst hPolyPiece1 (hPolyPiece2 h) ≫
      chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h) =
    pullback.snd hPolyPiece1 (hPolyPiece2 h) ≫
      chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)
  have hpb : IsPullback (hPolyIntToChart1 h) (hPolyIntToChart2 h) hPolyPiece1 (hPolyPiece2 h) :=
    IsOpenImmersion.isPullback (hPolyIntToChart1 h) (hPolyIntToChart2 h) hPolyPiece1
      (hPolyPiece2 h) (hPolyInt_square1 h) (hPolyInt_preimage_piece1 h)
  haveI : HasPullback hPolyPiece1 (hPolyPiece2 h) := inferInstance
  let e := hpb.isoPullback
  have h1 : e.hom ≫ pullback.fst hPolyPiece1 (hPolyPiece2 h) = hPolyIntToChart1 h :=
    IsPullback.isoPullback_hom_fst hpb
  have h2 : e.hom ≫ pullback.snd hPolyPiece1 (hPolyPiece2 h) = hPolyIntToChart2 h :=
    IsPullback.isoPullback_hom_snd hpb
  haveI : Epi e.hom := inferInstance
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← Category.assoc, h1, h2]
  rw [hPolyIntToChart1_chartMorphismInf h (hPolyT h),
    hPolyIntToChart2_chartMorphism0 h (hPolyLam h)]
  exact hPolyInt_transport h

/-- Compatibility of the chart morphisms of pieces 0 and 2. -/
theorem compat_c0_c2 (h : Polynomial ℚ) (hh : h ≠ 0) :
    pullback.fst (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) ≫ hPolyChartOf h HIdx.c0 =
      pullback.snd (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2) ≫
        hPolyChartOf h HIdx.c2 := by
  show pullback.fst hPolyPiece0 (hPolyPiece2 h) ≫ chartMorphismInf (R := Polynomial ℚ) h =
    pullback.snd hPolyPiece0 (hPolyPiece2 h) ≫
      chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)
  have hpb : IsPullback (hPolyIntToChart0 h) (hPolyIntToChart2 h) hPolyPiece0 (hPolyPiece2 h) :=
    IsOpenImmersion.isPullback (hPolyIntToChart0 h) (hPolyIntToChart2 h) hPolyPiece0
      (hPolyPiece2 h) (hPolyInt_square0 h) (hPolyInt_preimage_piece0 h)
  haveI : HasPullback hPolyPiece0 (hPolyPiece2 h) := inferInstance
  let e := hpb.isoPullback
  have h1 : e.hom ≫ pullback.fst hPolyPiece0 (hPolyPiece2 h) = hPolyIntToChart0 h :=
    IsPullback.isoPullback_hom_fst hpb
  have h2 : e.hom ≫ pullback.snd hPolyPiece0 (hPolyPiece2 h) = hPolyIntToChart2 h :=
    IsPullback.isoPullback_hom_snd hpb
  haveI : Epi e.hom := inferInstance
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← Category.assoc, h1, h2]
  rw [hPolyIntToChart0_chartMorphismInf h, hPolyIntToChart2_chartMorphism0 h (hPolyLam h),
    evalAt_tau_h h hh, hPolyInt_algMap_hPolyLam h]
  exact (chartMorphism_transition (R := hPolyIntRing h) (hPolyIntUnit h)).symm

/-- Diagonal compatibility: a piece is compatible with itself. -/
theorem compat_diag {X : Scheme} (f : X ⟶ projectiveLineGlued) (c : X ⟶ projectiveLineGlued)
    [IsOpenImmersion f] :
    pullback.fst f f ≫ c = pullback.snd f f ≫ c := by
  have hfs : pullback.fst f f = pullback.snd f f := by
    rw [← cancel_mono f, pullback.condition]
  rw [hfs]

/-- Compatibility of a transposed pair of pieces, from the compatibility of the pair. -/
theorem compat_swap {X Y : Scheme} (f : X ⟶ projectiveLineGlued) (g : Y ⟶ projectiveLineGlued)
    (cX : X ⟶ projectiveLineGlued) (cY : Y ⟶ projectiveLineGlued)
    (H : pullback.fst f g ≫ cX = pullback.snd f g ≫ cY) :
    pullback.fst g f ≫ cY = pullback.snd g f ≫ cX := by
  haveI : Epi (pullbackSymmetry f g).hom := inferInstance
  rw [← cancel_epi (pullbackSymmetry f g).hom]
  rw [← Category.assoc, ← Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  exact H.symm

/-- Compatibility of the chart morphisms on the pullback of any two pieces of the cover. -/
theorem hPoly_compat (h : Polynomial ℚ) (hh : h ≠ 0) :
    ∀ x y : (hPolyCover h hh).I₀,
      pullback.fst ((hPolyCover h hh).f x) ((hPolyCover h hh).f y) ≫ hPolyChartOf h x =
        pullback.snd ((hPolyCover h hh).f x) ((hPolyCover h hh).f y) ≫ hPolyChartOf h y := by
  intro x y
  simp only [hPolyCover_f]
  cases x <;> cases y
  · exact compat_diag (hPolyPieceMap h HIdx.c0) (hPolyChartOf h HIdx.c0)
  · exact compat_c0_c1 h hh
  · exact compat_c0_c2 h hh
  · exact compat_swap (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c1)
      (hPolyChartOf h HIdx.c0) (hPolyChartOf h HIdx.c1) (compat_c0_c1 h hh)
  · exact compat_diag (hPolyPieceMap h HIdx.c1) (hPolyChartOf h HIdx.c1)
  · exact compat_c1_c2 h hh
  · exact compat_swap (hPolyPieceMap h HIdx.c0) (hPolyPieceMap h HIdx.c2)
      (hPolyChartOf h HIdx.c0) (hPolyChartOf h HIdx.c2) (compat_c0_c2 h hh)
  · exact compat_swap (hPolyPieceMap h HIdx.c1) (hPolyPieceMap h HIdx.c2)
      (hPolyChartOf h HIdx.c1) (hPolyChartOf h HIdx.c2) (compat_c1_c2 h hh)
  · exact compat_diag (hPolyPieceMap h HIdx.c2) (hPolyChartOf h HIdx.c2)

/-- The scheme-level morphism hPoly : P^1 -> P^1 attached to a nonzero polynomial h. -/
noncomputable def hPoly (h : Polynomial ℚ) (hh : h ≠ 0) :
    projectiveLineGlued ⟶ projectiveLineGlued :=
  (hPolyCover h hh).glueMorphisms (hPolyChartOf h) (hPoly_compat h hh)

theorem hPoly_ι0 (h : Polynomial ℚ) (hh : h ≠ 0) :
    (hPolyCover h hh).f HIdx.c0 ≫ hPoly h hh = hPolyChartOf h HIdx.c0 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := hPolyCover h hh) (f := hPolyChartOf h)
    (hf := hPoly_compat h hh) HIdx.c0

theorem hPoly_ι1 (h : Polynomial ℚ) (hh : h ≠ 0) :
    (hPolyCover h hh).f HIdx.c1 ≫ hPoly h hh = hPolyChartOf h HIdx.c1 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := hPolyCover h hh) (f := hPolyChartOf h)
    (hf := hPoly_compat h hh) HIdx.c1

theorem hPoly_ι2 (h : Polynomial ℚ) (hh : h ≠ 0) :
    (hPolyCover h hh).f HIdx.c2 ≫ hPoly h hh = hPolyChartOf h HIdx.c2 :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := hPolyCover h hh) (f := hPolyChartOf h)
    (hf := hPoly_compat h hh) HIdx.c2

#print axioms eq_of_mul_eq_one_left
#print axioms hPolyIntUnit
#print axioms compat_c1_c2
#print axioms compat_c0_c2
#print axioms hPoly_compat
#print axioms hPoly
#print axioms hPoly_ι0
#print axioms hPoly_ι1
#print axioms hPoly_ι2


end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
-- t2
-- t3
-- t4
-- t5
-- t6
-- t7
