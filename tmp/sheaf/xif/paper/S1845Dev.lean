import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1845AlgEndActual

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual

abbrev S1845F := S1726K
abbrev S1845T : SchemeOverField S1845F := S1726AffineOver
abbrev S1845X : EtaleStackOverField S1845F := S1726Orbicurve.stack

theorem S1845BasePoint_eq :
    S1733BasePoint = (Pseudofunctor.StrongTrans.id S1845X.fiber :
      Pseudofunctor.StrongTrans S1845X.fiber S1845X.fiber) := rfl
abbrev S1845P : SchemeOverField S1845F :=
  Over.mk (Limits.coprod.desc S1845T.hom S1845T.hom)

noncomputable def S1845Fold : S1845P ⟶ S1845T :=
  Over.homMk (show Over.left S1845P ⟶ Over.left S1845T from
      Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left)) (by
    show Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left) ≫
        Over.hom S1845T = Over.hom S1845P
    rw [show Over.hom S1845P =
      Limits.coprod.desc (Over.hom S1845T) (Over.hom S1845T) from rfl]
    rw [Limits.coprod.desc_comp]
    simp)

noncomputable def S1845Inl : S1845T ⟶ S1845P :=
  Over.homMk (show Over.left S1845T ⟶ Over.left S1845P from Limits.coprod.inl) (by
    show Limits.coprod.inl ≫ Over.hom S1845P = Over.hom S1845T
    rw [show Over.hom S1845P =
      Limits.coprod.desc (Over.hom S1845T) (Over.hom S1845T) from rfl]
    rw [Limits.coprod.inl_desc])


noncomputable def S1845Inr : S1845T ⟶ S1845P :=
  Over.homMk (show Over.left S1845T ⟶ Over.left S1845P from Limits.coprod.inr) (by
    show Limits.coprod.inr ≫ Over.hom S1845P = Over.hom S1845T
    rw [show Over.hom S1845P =
      Limits.coprod.desc (Over.hom S1845T) (Over.hom S1845T) from rfl]
    rw [Limits.coprod.inr_desc])

theorem S1845Inl_fold : S1845Inl ≫ S1845Fold = 𝟙 S1845T := by
  apply Comma.hom_ext
  · show Limits.coprod.inl ≫ Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left) = 𝟙 S1845T.left
    rw [Limits.coprod.inl_desc]
  · apply Subsingleton.elim


theorem S1845Fold_finite : IsFinite (Over.Hom.left S1845Fold) := by
  change IsFinite (Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left))
  infer_instance

theorem S1845Fold_etale : Etale (Over.Hom.left S1845Fold) := by
  change Etale (Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left))
  let C := coprodOpenCover.{0, 0} (X := S1845T.left) (Y := S1845T.left)
  refine IsZariskiLocalAtSource.of_openCover C ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · change Etale (C.f (Sum.inl PUnit.unit) ≫ Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left))
    simp only [C, coprodOpenCover, Sum.elim_inl]
    rw [Limits.coprod.inl_desc]
    infer_instance
  · change Etale (C.f (Sum.inr PUnit.unit) ≫ Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left))
    simp only [C, coprodOpenCover, Sum.elim_inr]
    rw [Limits.coprod.inr_desc]
    infer_instance

noncomputable def S1845FoldStrong :
    Pseudofunctor.StrongTrans (S1742YS (F := S1845F) S1845P) (S1742YS (F := S1845F) S1845T) :=
  S1742StrongTransOfHom S1845Fold

noncomputable def S1845InlStrong :
    Pseudofunctor.StrongTrans (S1742YS (F := S1845F) S1845T) (S1742YS (F := S1845F) S1845P) :=
  S1742StrongTransOfHom S1845Inl

noncomputable def S1845FoldMap : SchemeRepresentableMap S1845Fold where
  transformation := S1845FoldStrong
  app_eq := by
    intro U
    rfl

theorem S1845InlFold_app_eq {W : EtaleStackPseudofunctor S1845F}
    (A : Pseudofunctor.StrongTrans W (S1742YS (F := S1845F) S1845T)) :
    ∀ a, (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp A S1845InlStrong) S1845FoldStrong).app a = A.app a := by
  intro a
  apply CategoryTheory.Cat.ext
  refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y f => ?_)
  · let P : Opposite.unop a.as ⟶ S1845T := ((A.app a).toFunctor.obj X).as
    have hP : (A.app a).toFunctor.obj X = Discrete.mk P := Discrete.mk_as _
    rw [hP]
    change ((S1742StrongTransOfHom S1845Fold).app a).toFunctor.obj
      (((S1742StrongTransOfHom S1845Inl).app a).toFunctor.obj (Discrete.mk P)) = Discrete.mk P
    rw [show (S1742StrongTransOfHom S1845Fold).app a = S1742App S1845Fold a from rfl]
    rw [show (S1742StrongTransOfHom S1845Inl).app a = S1742App S1845Inl a from rfl]
    rw [S1742App_obj, S1742App_obj]
    apply Discrete.ext
    rw [Category.assoc, S1845Inl_fold, Category.comp_id]
  · haveI : Subsingleton
        ((((A.vcomp S1845InlStrong).vcomp S1845FoldStrong).app a).toFunctor.obj X ⟶
          (((A.vcomp S1845InlStrong).vcomp S1845FoldStrong).app a).toFunctor.obj Y) := by
      change Subsingleton (Discrete.mk _ ⟶ Discrete.mk _)
      infer_instance
    exact Subsingleton.elim _ _

theorem S1845NonemptyIsoOfAppEq {W : EtaleStackPseudofunctor S1845F} {S : SchemeOverField S1845F}
    {L L' : Pseudofunctor.StrongTrans W (S1742YS (F := S1845F) S)}
    (h : ∀ a, L.app a = L'.app a) : Nonempty (L ≅ L') := by
  refine ⟨Pseudofunctor.StrongTrans.isoMk (fun a => eqToIso (h a)) ?_⟩
  intro a b f
  haveI : Subsingleton ((W.map f ≫ L.app b) ⟶ (L'.app a ≫ (S1742YS S).map f)) := by
    constructor
    intro alpha beta
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  exact Subsingleton.elim _ _

noncomputable abbrev S1845TwistSquare :
    EtalePseudofunctorSquare (S1742YS (F := S1845F) S1845P)
      S1845X.fiber (S1742YS (F := S1845F) S1845T) S1845X.fiber :=
  EtalePseudofunctorSquare.mk S1845FoldStrong S1845FoldMap.transformation
    (Pseudofunctor.StrongTrans.id S1845X.fiber)
    S1733BasePoint
    (Iso.refl _)

noncomputable def S1845ConeToXToY {W : EtaleStackPseudofunctor S1845F}
    (cone : (S1845TwistSquare).Cone W) : cone.toX ≅ cone.toY :=
  (Pseudofunctor.StrongTrans.rightUnitor cone.toX).symm.trans
    (cone.commutes.trans (Pseudofunctor.StrongTrans.rightUnitor cone.toY))

noncomputable def S1845TwistWitness : (S1845TwistSquare).TwoPullbackWitness where
  lift W cone := Pseudofunctor.StrongTrans.vcomp cone.toX S1845InlStrong
  liftToX W cone :=
    Classical.choice (S1845NonemptyIsoOfAppEq (S1845InlFold_app_eq cone.toX))
  liftToY W cone :=
    (Classical.choice (S1845NonemptyIsoOfAppEq (S1845InlFold_app_eq cone.toX))).trans
      (S1845ConeToXToY cone)
  liftTwoCell W source target morphism :=
    Pseudofunctor.StrongTrans.whiskerRight morphism.toX S1845InlStrong
  liftTwoCell_toX := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp source.toX S1845InlStrong) (S1845TwistSquare).toX) ⟶
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp target.toX S1845InlStrong) (S1845TwistSquare).toX)) :=
      S1800Modification_subsingleton (S := S1845T) _ _
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp source.toX S1845InlStrong) (S1845TwistSquare).toY) ⟶
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp target.toX S1845InlStrong) (S1845TwistSquare).toY)) :=
      S1800Modification_subsingleton (S := S1845T) _ _
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    haveI : Subsingleton (first ⟶ second) :=
      S1800Modification_subsingleton (S := S1845P) _ _
    exact Subsingleton.elim _ _

noncomputable def S1845TwistBaseChange :
    EtaleStackBaseChangePresentation (source := S1845X) (target := S1845X)
      (map := Pseudofunctor.StrongTrans.id S1845X.fiber) S1845T S1733BasePoint where
  pullbackScheme := S1845P
  projection := S1845Fold
  projectionMap := S1845FoldMap
  toSource := S1845FoldStrong
  commutes := by
    change (S1845TwistSquare).toX.vcomp (S1845TwistSquare).xToBase ≅
      (S1845TwistSquare).toY.vcomp (S1845TwistSquare).yToBase
    exact (S1845TwistSquare).commutes
  isPullback := by
    change (S1845TwistSquare).TwoPullbackWitness
    exact S1845TwistWitness


/-! ## Canonical identity base change -/

noncomputable def S1845IdRepMap (T : SchemeOverField S1845F) :
    SchemeRepresentableMap (𝟙 T) where
  transformation := Pseudofunctor.StrongTrans.id (S1742YS (F := S1845F) T)
  app_eq := by
    intro U
    apply CategoryTheory.Cat.ext
    apply Discrete.functor_ext
    intro P
    exact Discrete.ext (Category.comp_id P)

noncomputable def S1845IdSquare (T : SchemeOverField S1845F)
    (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber) :
    EtalePseudofunctorSquare (S1742YS (F := S1845F) T) S1845X.fiber
      (S1742YS (F := S1845F) T) S1845X.fiber :=
  EtalePseudofunctorSquare.mk q (S1845IdRepMap T).transformation
    (Pseudofunctor.StrongTrans.id S1845X.fiber) q
    ((Pseudofunctor.StrongTrans.rightUnitor q).trans
      (Pseudofunctor.StrongTrans.leftUnitor q).symm)

noncomputable def S1845IdWitness (T : SchemeOverField S1845F)
    (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber) :
    (S1845IdSquare T q).TwoPullbackWitness :=
  { lift := fun _ cone => cone.toY
    liftToX := fun _ cone =>
      (cone.commutes.symm).trans (Pseudofunctor.StrongTrans.rightUnitor cone.toX)
    liftToY := fun _ cone => Pseudofunctor.StrongTrans.rightUnitor cone.toY
    liftTwoCell := fun _ _ _ morphism => morphism.toY
    liftTwoCell_toX := by
      intro W source target morphism
      haveI : Subsingleton
          ((Pseudofunctor.StrongTrans.vcomp source.toY (S1845IdSquare T q).toX) ⟶
            (Pseudofunctor.StrongTrans.vcomp target.toY (S1845IdSquare T q).toX)) :=
        S1800Modification_subsingleton (S := S1845T) _ _
      exact Subsingleton.elim _ _
    liftTwoCell_toY := by
      intro W source target morphism
      haveI : Subsingleton
          ((Pseudofunctor.StrongTrans.vcomp source.toY (S1845IdSquare T q).toY) ⟶
            (Pseudofunctor.StrongTrans.vcomp target.toY (S1845IdSquare T q).toY)) :=
        S1800Modification_subsingleton (S := T) _ _
      exact Subsingleton.elim _ _
    twoCell_ext := by
      intro W first second alpha beta h1 h2
      haveI : Subsingleton (first ⟶ second) :=
        S1800Modification_subsingleton (S := T) _ _
      exact Subsingleton.elim _ _ }

noncomputable def S1845IdBaseChange (T : SchemeOverField S1845F)
    (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber) :
    EtaleStackBaseChangePresentation (source := S1845X) (target := S1845X)
      (map := Pseudofunctor.StrongTrans.id S1845X.fiber) T q where
  pullbackScheme := T
  projection := 𝟙 T
  projectionMap := S1845IdRepMap T
  toSource := q
  commutes :=
    (Pseudofunctor.StrongTrans.rightUnitor q).trans
      (Pseudofunctor.StrongTrans.leftUnitor q).symm
  isPullback := S1845IdWitness T q

/-! ## The piecewise base-change presentation -/

abbrev S1845Point :=
  Σ T : SchemeOverField S1845F,
    Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber

noncomputable def S1845BadBaseChange :
    ∀ (T : SchemeOverField S1845F)
      (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber),
      EtaleStackBaseChangePresentation (source := S1845X) (target := S1845X)
        (map := Pseudofunctor.StrongTrans.id S1845X.fiber) T q :=
  fun T q => by
    classical
    let P : S1845Point → Type _ := fun s =>
      EtaleStackBaseChangePresentation (source := S1845X) (target := S1845X)
        (map := Pseudofunctor.StrongTrans.id S1845X.fiber) s.1 s.2
    have hP : P ⟨S1845T, S1733BasePoint⟩ := S1845TwistBaseChange
    change P ⟨T, q⟩
    exact
      if h : (⟨T, q⟩ : S1845Point) = ⟨S1845T, S1733BasePoint⟩ then
        h ▸ hP
      else
        S1845IdBaseChange T q


abbrev S1845PresentedPoint (T : SchemeOverField S1845F)
    (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber) : Type _ :=
  { P : EtaleStackBaseChangePresentation (source := S1845X) (target := S1845X)
      (map := Pseudofunctor.StrongTrans.id S1845X.fiber) T q //
    IsFinite (Over.Hom.left P.projection) ∧ Etale (Over.Hom.left P.projection) }

noncomputable def S1845TwistBad : S1845PresentedPoint S1845T S1733BasePoint :=
  ⟨S1845TwistBaseChange, S1845Fold_finite, S1845Fold_etale⟩

noncomputable def S1845IdBad (T : SchemeOverField S1845F)
    (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber) :
    S1845PresentedPoint T q :=
  ⟨S1845IdBaseChange T q, by
    change IsFinite (Over.Hom.left (𝟙 T))
    infer_instance, by
    change Etale (Over.Hom.left (𝟙 T))
    infer_instance⟩

noncomputable def S1845BadData (T : SchemeOverField S1845F)
    (q : Pseudofunctor.StrongTrans (S1742YS (F := S1845F) T) S1845X.fiber) :
    S1845PresentedPoint T q := by
  classical
  let M : S1845Point → Type _ := fun s => S1845PresentedPoint s.1 s.2
  have hT : M ⟨S1845T, S1733BasePoint⟩ := S1845TwistBad
  change M ⟨T, q⟩
  exact
    if h : (⟨T, q⟩ : S1845Point) = ⟨S1845T, S1733BasePoint⟩ then
      h ▸ hT
    else
      S1845IdBad T q

noncomputable def S1845BadFiniteEtale :
    EtaleStackFiniteEtaleMorphism (source := S1845X) (target := S1845X)
      (Pseudofunctor.StrongTrans.id S1845X.fiber) where
  baseChange T q := (S1845BadData T q).1
  hasProperty T q := (S1845BadData T q).2

noncomputable def S1845BadCover :
    LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728Cover :=
  OrbicurveFiniteEtaleCover.mk S1845X
    (Pseudofunctor.StrongTrans.id S1845X.fiber) S1845BadFiniteEtale


theorem S1845BadData_twist :
    S1845BadData S1845T S1733BasePoint = S1845TwistBad := by
  simp [S1845BadData]

theorem S1845BadBaseChange_eq :
    S1845BadCover.finiteEtale.baseChange S1726AffineOver S1733BasePoint =
      S1845TwistBaseChange := by
  change (S1845BadData S1845T S1733BasePoint).1 = S1845TwistBaseChange
  rw [S1845BadData_twist]
  rfl

theorem S1845Bad_model : S1733Model S1845BadCover = S1845P := by
  unfold S1733Model
  rw [S1845BadBaseChange_eq]
  rfl

theorem S1845Bad_modelOver :
    S1845Bad_model ▸ S1733ModelOver S1845BadCover = S1845Fold := by
  cases S1845Bad_model
  unfold S1733ModelOver
  rw [S1845BadBaseChange_eq]
  rfl

theorem S1845Bad_toSource :
    S1845Bad_model ▸ S1756ToSource S1845BadCover = S1845FoldStrong := by
  cases S1845Bad_model
  unfold S1756ToSource S1743BaseChange
  rw [S1845BadBaseChange_eq]
  rfl

theorem S1845Bad_lift :
    S1845Bad_model ▸ S1743Lift S1845BadCover =
      Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743Y (F := S1845F) S1845T)) S1845InlStrong := by
  cases S1845Bad_model
  unfold S1743Lift S1743BaseChange S1743IdentityCone
  rw [S1845BadBaseChange_eq]
  rfl

theorem S1845Bad_end :
    S1845Bad_model ▸ S1756End S1845BadCover = S1845Fold ≫ S1845Inl := by
  cases S1845Bad_model
  unfold S1756End S1756ToSource S1743Lift S1743BaseChange S1743IdentityCone
  rw [S1845BadBaseChange_eq]
  rw [S1743YonedaEval_vcomp]
  rw [S1743YonedaEval_vcomp, S1756YonedaEval_id,
    S1742HomOfStrongTrans_strongTransOfHom, Category.id_comp]
  rw [S1742HomOfStrongTrans_strongTransOfHom]

theorem S1845Bad_end_ne : S1756End S1845BadCover ≠ 𝟙 (S1733Model S1845BadCover) := by
  intro h
  have h' : S1845Bad_model ▸ S1756End S1845BadCover =
      S1845Bad_model ▸ 𝟙 (S1733Model S1845BadCover) := congrArg (fun g => S1845Bad_model ▸ g) h
  rw [S1845Bad_end] at h'
  -- h' : fold ≫ inl = 𝟙 P
  rw [show S1845Bad_model ▸ (𝟙 (S1733Model S1845BadCover)) = 𝟙 S1845P from by
    cases S1845Bad_model
    rfl] at h'
  exact S1845FoldInl_ne_id h'

#check S1845BadCover
#check LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual.S1831AlgEnd S1845BadCover
#check LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual.S1756End S1845BadCover

theorem S1845Fold_left : Over.Hom.left S1845Fold =
    Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left) := rfl
theorem S1845Inl_left : Over.Hom.left S1845Inl = Limits.coprod.inl := rfl
theorem S1845Inr_left : Over.Hom.left S1845Inr = Limits.coprod.inr := rfl

theorem S1845FoldInl_ne_id : (S1845Fold ≫ S1845Inl) ≠ 𝟙 S1845P := by
  intro h
  have hleft : Over.Hom.left (S1845Fold ≫ S1845Inl) = Over.Hom.left (𝟙 S1845P) :=
    congrArg Over.Hom.left h
  rw [Over.comp_left, Over.id_left] at hleft
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  let x : S1845T.left := Classical.choice hne
  let y : S1845P.left :=
    (Limits.coprod.inr : S1845T.left ⟶ (S1845T.left ⨿ S1845T.left)) x
  have hx := congrArg (fun f : S1845P.left ⟶ S1845P.left => f y) hleft
  change (Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left) ≫ Limits.coprod.inl) y =
    (𝟙 S1845P.left) y at hx
  rw [Scheme.Hom.comp_apply] at hx
  rw [show (Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left)) y =
      (Limits.coprod.inr ≫ Limits.coprod.desc (𝟙 S1845T.left) (𝟙 S1845T.left)) x from rfl,
    Limits.coprod.inr_desc] at hx
  simp only [CategoryTheory.id_apply] at hx
  exact (AlgebraicGeometry.inl_ne_inr (S1845T.left) (S1845T.left) x x) hx

example : S1845BadData S1845T S1733BasePoint = S1845TwistBad := by
  simp [S1845BadData]

example : (S1845BadData S1845T S1733BasePoint).1 = S1845TwistBaseChange := by
  rw [show S1845BadData S1845T S1733BasePoint = S1845TwistBad from by simp [S1845BadData]]
  rfl

example : S1733Model S1845BadCover = S1845P := by
  unfold S1733Model
  rw [show (S1845BadCover.finiteEtale.baseChange S1726AffineOver S1733BasePoint) =
      (S1845BadData S1845T S1733BasePoint).1 from rfl]
  rw [show (S1845BadData S1845T S1733BasePoint).1 = S1845TwistBaseChange from by
    rw [show S1845BadData S1845T S1733BasePoint = S1845TwistBad from by simp [S1845BadData]]
    rfl]
  rfl

end LeanFormal.IUT.XiFPaper.S1845AlgEndActual