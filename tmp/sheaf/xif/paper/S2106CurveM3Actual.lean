/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import tmp.sheaf.xif.paper.S2087AffineQuotientPackagingActual
import tmp.sheaf.xif.paper.S2088FiberFunctorCertificateActual
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# S2106 -- M3 of the curve CardV: pullbacks and finite coproducts proved, and
  the exact status of the other three type-level fields

Target (frozen in S2070 and isolated in S2088): for a field K, a field Omega and a
geometric point x : Spec Omega -> CurveBase K, the five type-level fields of
RemainingTypeLevel K Omega x for the actual geometric fiber functor
curveGeometricFiberFunctor K Omega x : FiniteEtaleCover (CurveBase K) -> Type u,
namely

  preservesPullbacks, preservesFiniteCoproducts, preservesEpis,
  preservesQuotientsByFiniteGroups (finite A), reflectsIsos.

## Results of this file

1. preservesPullbacks: PROVED unconditionally (Type level, hence for the
   FintypeCat-valued lift by S2088 given GeometricFiberFinite).  For a cospan
   f : X -> Z and g : Y -> Z of finite etale covers we take the explicit scheme
   pullback cover of Example36CurveGaloisCategory and show, using
   Types.isPullback_iff, that its image square in Type is a pullback: a pair of
   lifts of the geometric point to X and Y which agree in Z is exactly a lift to
   the scheme pullback over X.

2. preservesFiniteCoproducts: PROVED unconditionally (Type level, hence
   FintypeCat level).  A binary coproduct of covers has underlying scheme the
   scheme coproduct; the two coproduct inclusions are disjoint open immersions
   (isCompl_range_inl_inr), and Spec Omega has a single point, so a lift of the
   geometric point to the coproduct lands in exactly one summand and factors
   through it uniquely (IsOpenImmersion.lift).  The initial cover has empty
   fiber.  Mathlib's PreservesFiniteCoproducts.of_preserves_binary_and_initial
   then gives all finite coproducts.

3. preservesEpis, preservesQuotientsByFiniteGroups and reflectsIsos: NOT
   PROVED, because as frozen they are FALSE.  The counterexample is at
   K = Omega = Q and the rational point x = (0,0) of y^2 = x^3 - x.

   Let K' = Q(sqrt 2) and let Y be the base change of CurveBase Q along the
   nontrivial finite etale morphism Spec K' -> Spec Q; the projection
   f : Y -> CurveBase Q is finite etale and surjective on underlying spaces.

   * preservesEpis fails: f is an epimorphism of finite etale covers (the image
     of a finite etale morphism is open and closed, and the equalizer of two
     maps out of the reduced curve is a closed subscheme containing the
     surjective image).  But the induced map on geometric fibers is
     F(f) : F(Y) -> F(X), where F(Y) is empty (a lift of x to Y is a
     Q-algebra map K' -> Q, which does not exist) and F(X) is the singleton
     {x}.  Hence F(f) is not surjective and F does not preserve epimorphisms.
   * reflectsIsos fails: let g : CurveBase Q coprod Y -> CurveBase Q be the
     fold (identity on the base, f on Y).  By the coproduct computation of
     item 2, F(CurveBase Q coprod Y) is the disjoint union of F(X) = {x} and
     F(Y) = empty, so F(g) is the identity of the singleton {x}, a bijection.
     But g is not an isomorphism, since Y is a nonempty component of the source
     disjoint from the base.
   * preservesQuotientsByFiniteGroups fails: the nontrivial deck
     transformation of the Galois cover Y -> CurveBase Q gives an action of
     A = Z/2 on Y whose colimit in the cover category is CurveBase Q.  The
     fiber functor sends this colimit to F(X) = {x}, while the colimit of the
     induced A-action on F(Y) = empty is empty.

   Consequently M3 cannot be closed with the frozen statements: no proof of
   the three fields for an arbitrary field Omega exists.  The mathematically
   correct hypothesis is that Omega is separably closed (a geometric point in
   the sense of Galois theory); under IsSepClosed Omega the three statements
   are the standard fiber-functor axioms.  The exact remaining inputs under
   that corrected hypothesis are recorded in the comment of section 8c.

## Honest boundary

No axiom, no sorry and no Nonempty wrapper around any target statement.  The
two proved fields are proved for the actual functor.  The three remaining
fields are stated verbatim in RemainingTypeLevelThree and used only as
hypotheses of conditional theorems.  No inhabitant of RemainingTypeLevelThree
is asserted.  The counterexample of item 3 is a mathematical argument
documented in this file; its formal interface is machine-checked in section 8b
(PreservesEpisCounterexample and ReflectsIsosCounterexample refute the two
frozen fields), but the construction of the specific cover at K = Omega = Q is
not formalized.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2106CurveM3Actual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Geometry
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.XiFPaper.S2081CurveCardM2Actual
open LeanFormal.IUT.XiFPaper.S2087AffineQuotientPackagingActual
open LeanFormal.IUT.XiFPaper.S2088FiberFunctorCertificateActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
universe u

abbrev curveFiber (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    CurveEtaleCoverCategory K ⥤ Type u :=
  curveGeometricFiberFunctor K Omega x


lemma structure_binaryCoproduct {K : Type u} [Field K] {A B : FiniteEtaleCover (CurveBase K)} :
    (binaryCoproductCover A B).1.hom =
      Limits.coprod.desc (A.1.hom) (B.1.hom) := rfl

lemma lift_inl_desc {X Y T Z : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ T)
    (z : Z ⟶ (X ⨿ Y : Scheme)) (h : Set.range z.base ⊆ Set.range (Limits.coprod.inl : X ⟶ (X ⨿ Y : Scheme))) :
    IsOpenImmersion.lift (Limits.coprod.inl : X ⟶ (X ⨿ Y : Scheme)) z h ≫ a =
      z ≫ Limits.coprod.desc a b := by
  calc IsOpenImmersion.lift (Limits.coprod.inl : X ⟶ (X ⨿ Y : Scheme)) z h ≫ a
      = IsOpenImmersion.lift (Limits.coprod.inl : X ⟶ (X ⨿ Y : Scheme)) z h ≫
          (Limits.coprod.inl ≫ Limits.coprod.desc a b) := by
        rw [Limits.coprod.inl_desc]
    _ = (IsOpenImmersion.lift (Limits.coprod.inl : X ⟶ (X ⨿ Y : Scheme)) z h ≫ Limits.coprod.inl) ≫
          Limits.coprod.desc a b := by
        rw [Category.assoc]
    _ = z ≫ Limits.coprod.desc a b := by
        rw [IsOpenImmersion.lift_fac]

lemma lift_inr_desc {X Y T Z : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ T)
    (z : Z ⟶ (X ⨿ Y : Scheme)) (h : Set.range z.base ⊆ Set.range (Limits.coprod.inr : Y ⟶ (X ⨿ Y : Scheme))) :
    IsOpenImmersion.lift (Limits.coprod.inr : Y ⟶ (X ⨿ Y : Scheme)) z h ≫ b =
      z ≫ Limits.coprod.desc a b := by
  calc IsOpenImmersion.lift (Limits.coprod.inr : Y ⟶ (X ⨿ Y : Scheme)) z h ≫ b
      = IsOpenImmersion.lift (Limits.coprod.inr : Y ⟶ (X ⨿ Y : Scheme)) z h ≫
          (Limits.coprod.inr ≫ Limits.coprod.desc a b) := by
        rw [Limits.coprod.inr_desc]
    _ = (IsOpenImmersion.lift (Limits.coprod.inr : Y ⟶ (X ⨿ Y : Scheme)) z h ≫ Limits.coprod.inr) ≫
          Limits.coprod.desc a b := by
        rw [Category.assoc]
    _ = z ≫ Limits.coprod.desc a b := by
        rw [IsOpenImmersion.lift_fac]

lemma range_subset_inl_of_mem {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (A B : FiniteEtaleCover (CurveBase K))
    (z : Spec (CommRingCat.of Omega) ⟶ (A.1.left ⨿ B.1.left : Scheme))
    (h : z.base default ∈ Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))) :
    Set.range z.base ⊆ Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) := by
  rintro _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p default]

lemma range_subset_inr_of_mem {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (A B : FiniteEtaleCover (CurveBase K))
    (z : Spec (CommRingCat.of Omega) ⟶ (A.1.left ⨿ B.1.left : Scheme))
    (h : z.base default ∈ Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))) :
    Set.range z.base ⊆ Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) := by
  rintro _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p default]

lemma mem_inr_of_not_mem_inl {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (A B : FiniteEtaleCover (CurveBase K))
    (z : Spec (CommRingCat.of Omega) ⟶ (A.1.left ⨿ B.1.left : Scheme))
    (h : z.base default ∉ Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))) :
    z.base default ∈ Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) := by
  have htop : Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) ∪
      Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) = Set.univ :=
    (isCompl_range_inl_inr A.1.left B.1.left).sup_eq_top
  have : z.base default ∈ (Set.univ : Set (A.1.left ⨿ B.1.left : Scheme)) := trivial
  rw [← htop] at this
  exact this.resolve_left h

noncomputable def coprodFiberInl {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K))
    (z : (curveFiber K Omega x).obj (binaryCoproductCover A B))
    (h : z.1.base default ∈ Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))) :
    (curveFiber K Omega x).obj A := by
  have hsub : Set.range z.1.base ⊆ Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) :=
    range_subset_inl_of_mem A B z.1 h
  refine ⟨IsOpenImmersion.lift (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
      z.1 hsub, ?_⟩
  have hmain : IsOpenImmersion.lift (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
      z.1 hsub ≫ A.1.hom = z.1 ≫ Limits.coprod.desc A.1.hom B.1.hom :=
    lift_inl_desc A.1.hom B.1.hom z.1 hsub
  exact hmain.trans z.2

noncomputable def coprodFiberInr {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K))
    (z : (curveFiber K Omega x).obj (binaryCoproductCover A B))
    (h : z.1.base default ∈ Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))) :
    (curveFiber K Omega x).obj B := by
  have hsub : Set.range z.1.base ⊆ Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) :=
    range_subset_inr_of_mem A B z.1 h
  refine ⟨IsOpenImmersion.lift (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
      z.1 hsub, ?_⟩
  have hmain : IsOpenImmersion.lift (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
      z.1 hsub ≫ B.1.hom = z.1 ≫ Limits.coprod.desc A.1.hom B.1.hom :=
    lift_inr_desc A.1.hom B.1.hom z.1 hsub
  exact hmain.trans z.2

noncomputable def coprodFiberToSum {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K))
    (z : (curveFiber K Omega x).obj (binaryCoproductCover A B)) :
    (curveFiber K Omega x).obj A ⊕ (curveFiber K Omega x).obj B := by
  classical
  exact if h : z.1.base default ∈
      Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) then
    Sum.inl (coprodFiberInl x A B z h)
  else
    Sum.inr (coprodFiberInr x A B z (mem_inr_of_not_mem_inl A B z.1 h))

noncomputable def sumToCoprodFiber {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K)) :
    (curveFiber K Omega x).obj A ⊕ (curveFiber K Omega x).obj B →
      (curveFiber K Omega x).obj (binaryCoproductCover A B) :=
  Sum.elim ((curveFiber K Omega x).map (binaryCoproductInl A B))
    ((curveFiber K Omega x).map (binaryCoproductInr A B))
theorem coprodFiberToSum_inl {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K)) (a : (curveFiber K Omega x).obj A) :
    coprodFiberToSum x A B ((curveFiber K Omega x).map (binaryCoproductInl A B) a) = Sum.inl a := by
  have hmem : ((curveFiber K Omega x).map (binaryCoproductInl A B) a).1.base default ∈
      Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) :=
    ⟨a.1.base default, rfl⟩
  have hsub := range_subset_inl_of_mem A B
    ((curveFiber K Omega x).map (binaryCoproductInl A B) a).1 hmem
  rw [coprodFiberToSum, dif_pos hmem]
  congr 1
  apply Subtype.ext
  exact (IsOpenImmersion.lift_uniq (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
    ((curveFiber K Omega x).map (binaryCoproductInl A B) a).1 hsub a.1 rfl).symm

theorem coprodFiberToSum_inr {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K)) (b : (curveFiber K Omega x).obj B) :
    coprodFiberToSum x A B ((curveFiber K Omega x).map (binaryCoproductInr A B) b) = Sum.inr b := by
  have hmem : ((curveFiber K Omega x).map (binaryCoproductInr A B) b).1.base default ∈
      Set.range (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) :=
    ⟨b.1.base default, rfl⟩
  have hnot : ((curveFiber K Omega x).map (binaryCoproductInr A B) b).1.base default ∉
      Set.range (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme)) := by
    intro hinl
    exact (Set.disjoint_left.mp (isCompl_range_inl_inr A.1.left B.1.left).disjoint) hinl hmem
  have hsub := range_subset_inr_of_mem A B
    ((curveFiber K Omega x).map (binaryCoproductInr A B) b).1 hmem
  rw [coprodFiberToSum, dif_neg hnot]
  congr 1
  apply Subtype.ext
  exact (IsOpenImmersion.lift_uniq (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
    ((curveFiber K Omega x).map (binaryCoproductInr A B) b).1 hsub b.1 rfl).symm

theorem sumToCoprodFiber_coprodFiberToSum {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K))
    (z : (curveFiber K Omega x).obj (binaryCoproductCover A B)) :
    sumToCoprodFiber x A B (coprodFiberToSum x A B z) = z := by
  rw [coprodFiberToSum]
  split_ifs with h
  · apply Subtype.ext
    exact IsOpenImmersion.lift_fac (Limits.coprod.inl : A.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
      z.1 (range_subset_inl_of_mem A B z.1 h)
  · apply Subtype.ext
    exact IsOpenImmersion.lift_fac (Limits.coprod.inr : B.1.left ⟶ (A.1.left ⨿ B.1.left : Scheme))
      z.1 (range_subset_inr_of_mem A B z.1 (mem_inr_of_not_mem_inl A B z.1 h))
noncomputable def binaryCofan_isColimit_image {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K)) :
    IsColimit (BinaryCofan.mk ((curveFiber K Omega x).map (binaryCoproductInl A B))
      ((curveFiber K Omega x).map (binaryCoproductInr A B))) := by
  refine (Types.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩ |>.some
  · intro a a' h
    have h' : (curveFiber K Omega x).map (binaryCoproductInl A B) a =
        (curveFiber K Omega x).map (binaryCoproductInl A B) a' := h
    have hc := congrArg (coprodFiberToSum x A B) h'
    rw [coprodFiberToSum_inl, coprodFiberToSum_inl, Sum.inl.injEq] at hc
    exact hc
  · intro b b' h
    have h' : (curveFiber K Omega x).map (binaryCoproductInr A B) b =
        (curveFiber K Omega x).map (binaryCoproductInr A B) b' := h
    have hc := congrArg (coprodFiberToSum x A B) h'
    rw [coprodFiberToSum_inr, coprodFiberToSum_inr, Sum.inr.injEq] at hc
    exact hc
  · constructor
    · rw [Set.disjoint_left]
      intro z hz1 hz2
      obtain ⟨a, ha⟩ := hz1
      obtain ⟨b, hb⟩ := hz2
      have h1 : (curveFiber K Omega x).map (binaryCoproductInl A B) a =
          (curveFiber K Omega x).map (binaryCoproductInr A B) b := ha.trans hb.symm
      have hcontra : (Sum.inl a : (curveFiber K Omega x).obj A ⊕ (curveFiber K Omega x).obj B) =
          Sum.inr b := by
        have := congrArg (coprodFiberToSum x A B) h1
        rw [coprodFiberToSum_inl, coprodFiberToSum_inr] at this
        exact this
      cases hcontra
    · rw [codisjoint_iff]
      change Set.range ⇑((curveFiber K Omega x).map (binaryCoproductInl A B)) ∪
        Set.range ⇑((curveFiber K Omega x).map (binaryCoproductInr A B)) = Set.univ
      rw [Set.eq_univ_iff_forall]
      intro z
      cases hz : coprodFiberToSum x A B z with
      | inl a =>
          refine Set.mem_union_left _ ⟨a, ?_⟩
          rw [← sumToCoprodFiber_coprodFiberToSum x A B z, hz]
          rfl
      | inr b =>
          refine Set.mem_union_right _ ⟨b, ?_⟩
          rw [← sumToCoprodFiber_coprodFiberToSum x A B z, hz]
          rfl

theorem preservesColimit_pair {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K)
    (A B : FiniteEtaleCover (CurveBase K)) :
    PreservesColimit (pair A B) (curveFiber K Omega x) :=
  preservesColimit_of_preserves_colimit_cocone (binaryCoproductIsColimit A B)
    ((isColimitMapCoconeBinaryCofanEquiv (curveFiber K Omega x)
      (binaryCoproductInl A B) (binaryCoproductInr A B)).symm
      (binaryCofan_isColimit_image x A B))

noncomputable instance preservesBinaryCoproducts_typeLevel {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    PreservesColimitsOfShape (Discrete WalkingPair) (curveFiber K Omega x) where
  preservesColimit := by
    intro Kd
    haveI := preservesColimit_pair x (Kd.obj ⟨WalkingPair.left⟩) (Kd.obj ⟨WalkingPair.right⟩)
    exact preservesColimit_of_iso_diagram (curveFiber K Omega x) (diagramIsoPair Kd).symm
noncomputable def isInitial_fiber_initialCover {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    IsInitial ((curveFiber K Omega x).obj (initialCover (S := CurveBase K))) := by
  haveI hempty : IsEmpty ((curveFiber K Omega x).obj (initialCover (S := CurveBase K))) := by
    refine ⟨fun s => ?_⟩
    exact initial_isEmpty.elim (s.1.base default)
  refine IsInitial.ofUniqueHom (fun Y => TypeCat.ofHom (fun x => isEmptyElim x)) ?_
  intro Y m
  ext x
  exact isEmptyElim x

noncomputable instance preservesEmpty_typeLevel {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    PreservesColimit (Functor.empty.{0} (CurveEtaleCoverCategory K)) (curveFiber K Omega x) where
  preserves := by
    intro c hc
    have hinit : IsInitial c.pt :=
      isColimitChangeEmptyCocone (C := CurveEtaleCoverCategory K) hc (asEmptyCocone c.pt) (Iso.refl _)
    have hiso : c.pt ≅ initialCover (S := CurveBase K) :=
      hinit.uniqueUpToIso (initialCoverIsInitial (S := CurveBase K))
    have hinit' : IsInitial ((curveFiber K Omega x).obj c.pt) :=
      IsInitial.ofIso (isInitial_fiber_initialCover (K := K) (Omega := Omega) x)
        ((curveFiber K Omega x).mapIso hiso.symm)
    exact ⟨isColimitChangeEmptyCocone (C := Type u) hinit' ((curveFiber K Omega x).mapCocone c) (Iso.refl _)⟩

noncomputable instance preservesInitialShape_typeLevel {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (curveFiber K Omega x) :=
  preservesColimitsOfShape_pempty_of_preservesInitial _

noncomputable instance preservesFiniteCoproducts_typeLevel {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    PreservesFiniteCoproducts (curveFiber K Omega x) where
  preserves n := by
    haveI : HasFiniteCoproducts (CurveEtaleCoverCategory K) :=
      finiteEtaleCover_hasFiniteCoproducts (S := CurveBase K)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (curveFiber K Omega x) (Fin n)

/-! ## 6. Pullbacks of covers and their preservation -/

instance hasPullbacks_curveCovers (K : Type u) [Field K] :
    HasPullbacks (FiniteEtaleCover (CurveBase K)) :=
  finiteEtaleCoverHasPullbacks (CurveBase K)

lemma structure_pullbackCover {K : Type u} [Field K] {X Y Z : FiniteEtaleCover (CurveBase K)}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    finiteEtaleCoverStructure (finiteEtaleCoverPullbackCover f g) =
      pullback.fst f.1.left g.1.left ≫ finiteEtaleCoverStructure X := rfl

theorem pullback_image_isPullback {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    {X Y Z : FiniteEtaleCover (CurveBase K)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback ((curveFiber K Omega x).map (finiteEtaleCoverPullbackFirst f g))
      ((curveFiber K Omega x).map (finiteEtaleCoverPullbackSecond f g))
      ((curveFiber K Omega x).map f) ((curveFiber K Omega x).map g) := by
  have hcond : (finiteEtaleCoverPullbackFirst f g).1.left ≫ f.1.left =
      (finiteEtaleCoverPullbackSecond f g).1.left ≫ g.1.left :=
    congrArg (fun k => k.1.left) (finiteEtaleCoverPullbackCondition f g)
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext s
    apply Subtype.ext
    change (s.1 ≫ (finiteEtaleCoverPullbackFirst f g).1.left) ≫ f.1.left =
      (s.1 ≫ (finiteEtaleCoverPullbackSecond f g).1.left) ≫ g.1.left
    rw [Category.assoc, Category.assoc, hcond]
  · intro s t hst
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hst.1
    · exact congrArg Subtype.val hst.2
  · intro a b hab
    have h : a.1 ≫ f.1.left = b.1 ≫ g.1.left := congrArg Subtype.val hab
    refine ⟨⟨pullback.lift a.1 b.1 h, ?_⟩, ?_, ?_⟩
    · show pullback.lift a.1 b.1 h ≫
        finiteEtaleCoverStructure (finiteEtaleCoverPullbackCover f g) = x
      rw [structure_pullbackCover]
      rw [pullback.lift_fst_assoc]
      exact a.2
    · apply Subtype.ext
      exact pullback.lift_fst a.1 b.1 h
    · apply Subtype.ext
      exact pullback.lift_snd a.1 b.1 h

theorem preservesPullbacks_typeLevel {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K} :
    PreservesLimitsOfShape WalkingCospan (curveFiber K Omega x) := by
  haveI := hasPullbacks_curveCovers (K := K)
  apply Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro X Y Z f g _
  exact ⟨finiteEtaleCoverPullbackCover f g, finiteEtaleCoverPullbackFirst f g,
    finiteEtaleCoverPullbackSecond f g,
    IsPullback.of_isLimit (finiteEtaleCoverPullbackIsLimitInCover f g),
    pullback_image_isPullback f g⟩

/-! ## 7. The two FintypeCat-valued certificate fields -/

theorem certificate_preservesPullbacks_m3 {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hfin : GeometricFiberFinite K Omega x) :
    PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctorFintype K hfin) :=
  certificate_preservesPullbacks hfin
    (preservesPullbacks_typeLevel (K := K) (Omega := Omega) (x := x))

theorem certificate_preservesFiniteCoproducts_m3 {K : Type u} [Field K] {Omega : Type u}
    [Field Omega] {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hfin : GeometricFiberFinite K Omega x) :
    PreservesFiniteCoproducts (curveGeometricFiberFunctorFintype K hfin) :=
  certificate_preservesFiniteCoproducts hfin
    (preservesFiniteCoproducts_typeLevel (K := K) (Omega := Omega) (x := x))

/-! ## 8. The exact remaining type-level fields -/

structure RemainingTypeLevelThree (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) : Prop where
  /-- (G5) preservation of epimorphisms. -/
  preservesEpis : Functor.PreservesEpimorphisms (curveFiber K Omega x)
  /-- (G5) preservation of quotients by finite groups. -/
  preservesQuotientsByFiniteGroups : forall (A : Type u) [Group A] [Finite A],
    PreservesColimitsOfShape (SingleObj A) (curveFiber K Omega x)
  /-- (G6) reflection of isomorphisms. -/
  reflectsIsos : (curveFiber K Omega x).ReflectsIsomorphisms

theorem remainingTypeLevel_of_three {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (h : RemainingTypeLevelThree K Omega x) :
    RemainingTypeLevel K Omega x where
  preservesPullbacks := preservesPullbacks_typeLevel
  preservesFiniteCoproducts := preservesFiniteCoproducts_typeLevel (K := K) (Omega := Omega) x
  preservesEpis := h.preservesEpis
  preservesQuotientsByFiniteGroups := h.preservesQuotientsByFiniteGroups
  reflectsIsos := h.reflectsIsos

theorem certificate_of_remaining_three {K : Type u} [Field K] {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hfin : GeometricFiberFinite K Omega x) (h : RemainingTypeLevelThree K Omega x) :
    FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin) :=
  certificate_of_remaining hfin (remainingTypeLevel_of_three h)

/-! ## 8c. What remains after correcting the hypothesis to IsSepClosed Omega

The three frozen fields are the fiber-functor axioms at a *geometric* point.
With the corrected hypothesis [IsSepClosed Omega] they become true, and the
exact inputs still missing from Mathlib 4.32.2 / this tree are:

* preservesEpis.  For an epimorphism f : Y -> Z of finite etale covers one must
  show that every Omega-point z of Z lifts to Y.  With Omega separably closed
  the fiber Y x_Z Spec Omega is Spec of a finite etale Omega-algebra, and the
  missing input is: a nonzero finite etale algebra over a separably closed
  field is a product of copies of the field (equivalently, every nonempty
  finite etale cover of Spec Omega has an Omega-point).  This is not in
  Mathlib 4.32.2.  One also needs the scheme-theoretic step epi => surjective
  on underlying spaces: the image of a finite etale morphism is open and
  closed, and the equalizer of two maps out of the reduced curve is a closed
  subscheme, so a closed image-complement cannot be nonempty.

* preservesQuotientsByFiniteGroups.  The quotient covers and their universal
  property are already available unconditionally: S2072/S2073/S2087 construct
  the affine action cocone and prove CurveQuotientsByFiniteGroups (S2087,
  curveHasQuotients).  What is missing is the comparison
  F(quotient) = quotient(F) at the geometric point, for a finite group A
  acting on a cover Y.  This needs the same splitting input at Omega and the
  identification of the fiber of the explicit affine quotient cover with the
  invariants of the fiber; S2087 constructs the quotient as the colimit of an
  explicit affine action cocone, so this computation is reachable there.

* reflectsIsos.  Needs that the fiber cardinality of a finite etale morphism is
  locally constant (so that a degree-one finite etale morphism is an
  isomorphism), and that a bijection on Omega-points for a separably closed
  Omega forces the degree to be one.  Neither the local constancy of the fiber
  cardinality nor finite etale of degree one is an isomorphism is in Mathlib
  4.32.2 or in the tree.

In dependency order, the first missing input under the corrected hypothesis is
the splitting of finite etale algebras over a separably closed field (for
preservesEpis), then the quotient-fiber comparison, then the local constancy of
the finite etale fiber cardinality (for reflectsIsos).
-/

/-! ## 8b. Machine-checked refutation interfaces for the frozen fields

The three structures below record exactly what a counterexample to the frozen
statements must consist of.  The two theorems show that such data refutes the
frozen field.  The mathematical counterexample documented in the module
header supplies this data at K = Omega = Q (with Y the base change of the curve
along Q(sqrt 2)); constructing that cover is not formalized here.
-/

/-- Data refuting `preservesEpis` at a geometric point: an epimorphism of
finite etale covers whose source fiber at the point is empty while the target
fiber is `{x}`. -/
structure PreservesEpisCounterexample (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) where
  /-- the source cover -/
  Y : FiniteEtaleCover (CurveBase K)
  /-- the epimorphism, to the terminal cover -/
  f : Y ⟶ terminalCover (CurveBase K)
  /-- it is an epimorphism -/
  epi : Epi f
  /-- its geometric fiber is empty -/
  fiber_empty : IsEmpty ((curveFiber K Omega x).obj Y)

theorem not_preservesEpis_of_counterexample {K : Type u} [Field K] {Omega : Type u}
    [Field Omega] {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (h : PreservesEpisCounterexample K Omega x) :
    ¬ Functor.PreservesEpimorphisms (curveFiber K Omega x) := by
  intro hpres
  haveI : Functor.PreservesEpimorphisms (curveFiber K Omega x) := hpres
  haveI : Epi h.f := h.epi
  haveI : Epi ((curveFiber K Omega x).map h.f) := Functor.map_epi (curveFiber K Omega x) h.f
  have hsurj : Function.Surjective ⇑(ConcreteCategory.hom ((curveFiber K Omega x).map h.f)) :=
    (epi_iff_surjective _).mp inferInstance
  have hz : (curveFiber K Omega x).obj (terminalCover (CurveBase K)) := ⟨x, Category.comp_id x⟩
  obtain ⟨y, -⟩ := hsurj hz
  exact h.fiber_empty.false y

/-- Data refuting `reflectsIsos` at a geometric point: a morphism which is
not an isomorphism but whose induced map on geometric fibers is a bijection. -/
structure ReflectsIsosCounterexample (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) where
  /-- the source cover -/
  Y : FiniteEtaleCover (CurveBase K)
  /-- the target cover -/
  Z : FiniteEtaleCover (CurveBase K)
  /-- the morphism -/
  f : Y ⟶ Z
  /-- its image on geometric fibers is a bijection -/
  bij : Function.Bijective ⇑(ConcreteCategory.hom ((curveFiber K Omega x).map f))
  /-- it is not an isomorphism -/
  notIso : ¬ IsIso f

theorem not_reflectsIsos_of_counterexample {K : Type u} [Field K] {Omega : Type u}
    [Field Omega] {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (h : ReflectsIsosCounterexample K Omega x) :
    ¬ (curveFiber K Omega x).ReflectsIsomorphisms := by
  intro hrefl
  haveI : (curveFiber K Omega x).ReflectsIsomorphisms := hrefl
  haveI : IsIso ((curveFiber K Omega x).map h.f) := (isIso_iff_bijective _).mpr h.bij
  exact h.notIso (Functor.ReflectsIsomorphisms.reflects (curveFiber K Omega x) h.f)

/-! ## 9. Consumer: the card from the three remaining fields -/

theorem s2106_cardV_of_remaining_three (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (h : RemainingTypeLevelThree K Omega x)
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    Nonempty (CurveEtaleFundamentalGroupCardV K) :=
  curveEtaleFundamentalGroupCardV_realized_of_remaining
    (s2073AffineActionCoconeIsColimit (curveCoordinateRing K))
    (s2081_geometricFiberFinite K (Omega := Omega) (x := x))
    (remainingTypeLevel_of_three h) geomPi geomConn

/-! ## 10. Axiom audit -/

#print axioms preservesPullbacks_typeLevel
#print axioms pullback_image_isPullback
#print axioms preservesFiniteCoproducts_typeLevel
#print axioms certificate_preservesPullbacks_m3
#print axioms certificate_preservesFiniteCoproducts_m3
#print axioms remainingTypeLevel_of_three
#print axioms certificate_of_remaining_three
#print axioms s2106_cardV_of_remaining_three
#print axioms not_preservesEpis_of_counterexample
#print axioms not_reflectsIsos_of_counterexample

end LeanFormal.IUT.XiFPaper.S2106CurveM3Actual
end