/-
# S1850: S1756FirstMissing is false

## The question

S1756 records the "first missing" statement of the affine route:

    S1756FirstMissing : Prop := ∀ A : S1728Cover, S1756End A = 𝟙 (S1733Model A)

(S1756CoverSourceRepresentabilityActual, Section 6).  S1756 proves that this single
scheme-level equation is exactly the missing unit 2-cell
`toSource ≫ lift ≅ 𝟙` (`S1756Unit_iff_end`), equivalently S1743's source
retraction (`S1756Retraction_iff_firstMissing`), and that any one-sided inverse
of the comparison forces it (`S1756End_eq_one_of_retraction`).  S1845Dev
(unverified) proposed to refute it with the terminal cover carrying a "doubled"
identity-point presentation; that file does not compile.

## What is proved here

1. A **uniform doubled base-change presentation** `S1850Doubled` for the
   identity map of the S1726 orbicurve, at *every* test scheme `T` and point
   `q`:

       pullbackScheme = T ⨿ T,   projection = fold,   toSource = fold ≫ q,

   together with a genuine `EtaleStackBaseChangePresentation` including a full
   `EtalePseudofunctorSquare.TwoPullbackWitness`
   (`S1850Doubled`, `S1850Witness`).  The key point that makes the construction
   work syntactically is that the presentation is *uniform* in `q`; no `if` on
   an undecidable equality of test points (as in S1845Dev) is used, so all the
   endomorphism computations below are definitional.

2. The projection `fold : T ⨿ T ⟶ T` is finite and etale (`S1850Fold_finite`,
   `S1850Fold_etale`), hence `S1850DoubledFiniteEtale` is a legal
   `EtaleStackFiniteEtaleMorphism` and `S1850DoubledCover : S1728Cover` is a
   legal `OrbicurveFiniteEtaleCover` (`S1850DoubledCover`).  Its source and map
   are *the same* as the S1839/S1762 terminal cover (`S1850SameSource`,
   `S1850SameMap`).

3. Its identity-point model is the coproduct `Spec R' ⨿ Spec R'` with structure
   morphism `fold` (`S1850Model`, `S1850ModelOver`, both definitional), and its
   identity-point self-endomorphism is

       S1756End S1850DoubledCover = S1850Fold ≫ S1850Inl

   by `rfl` (`S1850End_direct`).  Since `fold ≫ inl ≠ 𝟙` for a nonempty base
   (`S1850FoldInl_ne_id`, using `Nontrivial R'` from S1844 and the two
   coproduct inclusions), the endomorphism is not the identity
   (`S1850End_ne`), and therefore

       ¬ S1756FirstMissing                        (S1850_not_firstMissing).

4. The refutation transports across the recorded equivalent models:

       ¬ S1841FirstMissing       (S1841's quasi-equivalence form),
       ¬ S1831AlgFirstMissing    (S1831's finite-etale-algebra form),
       ¬ S1845AlgEndTarget       (S1845's algebra endomorphism form),
       ¬ S1743SourceRetraction   (S1743's source retraction).

   It also shows the unit 2-cell itself fails for this cover
   (`S1850NoUnit`) and that no one-sided inverse exists (`S1850NoRetraction`).

## The exact diagnosis

The counterexample is produced by the *recorded definitions*, not by an added
axiom:

* `EtaleStackRepresentableMorphismProperty` asks only for a base-change
  presentation at each point; it has no coherence between different points.
* `EtalePseudofunctorSquare.TwoPullbackWitness` records a lift for every cone,
  the two comparison 2-cells, the action on cone morphisms and 2-cell
  extensionality, but **not** the uniqueness of the lift, nor the triangle
  identities tying the comparisons to the cone's own 2-cell.  The doubled
  square satisfies this weak witness, although its projection `fold` is not
  even an isomorphism (`S1850Fold_not_iso`), while the canonical presentation of
  the *same* map at the *same* point has projection `𝟙` (an isomorphism):
  `S1850Presentations_not_unique`.  Hence the recorded base-change datum does
  not determine `S1756End`, and no argument from that datum can prove
  `S1756FirstMissing`.

The geometric statement is therefore **not** refuted: the doubled presentation
is a legal inhabitant of the project's `S1728Cover` type but is not a coherent
finite-etale cover.  What is refuted is the formal affine route as recorded:
`S1756FirstMissing` is *false* on the actual `S1728Cover` type, so it cannot be
supplied as a theorem.  The exact missing input is the unit 2-cell
(`S1756Unit`, equivalently the full 2-pullback property); after strengthening
the cover datum by it, `S1756FirstMissing` holds by definition
(`S1756Unit_iff_end`), i.e. the remaining content is an assumption on the cover
presentation, not a consequence of the recorded weak witness.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the audit block at the
end.  No `sorry`, no `admit`, no new axiom.
-/

import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1845AlgEndActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1839SliceFillingActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
open LeanFormal.IUT.XiFPaper.S1845AlgEndActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual

/-! ## 1. The uniform doubled presentation -/

/-- The base field of the S1726 orbicurve. -/
abbrev S1850F := S1726K

/-- The actual S1726 orbicurve stack. -/
abbrev S1850X : EtaleStackOverField S1850F := S1726Orbicurve.stack

/-- The affine base of the S1726 model. -/
abbrev S1850T : SchemeOverField S1850F := S1726AffineOver

/-- The doubled test scheme `T ⨿ T`, as an object over the base.  The structure
map is the coproduct of the structure maps, so that its underlying scheme is the
scheme coproduct of the underlying schemes. -/
noncomputable def S1850P (T : SchemeOverField S1850F) : SchemeOverField S1850F :=
  Over.mk (Limits.coprod.desc T.hom T.hom)

/-- The fold `T ⨿ T ⟶ T`, i.e. the "doubled" projection. -/
noncomputable def S1850Fold (T : SchemeOverField S1850F) : S1850P T ⟶ T :=
  Over.homMk (show Over.left (S1850P T) ⟶ Over.left T from
      Limits.coprod.desc (𝟙 T.left) (𝟙 T.left)) (by
    show Limits.coprod.desc (𝟙 T.left) (𝟙 T.left) ≫ Over.hom T = Over.hom (S1850P T)
    rw [show Over.hom (S1850P T) =
      Limits.coprod.desc (Over.hom T) (Over.hom T) from rfl]
    rw [Limits.coprod.desc_comp]
    simp)

/-- The first inclusion `T ⟶ T ⨿ T`. -/
noncomputable def S1850Inl (T : SchemeOverField S1850F) : T ⟶ S1850P T :=
  Over.homMk (show Over.left T ⟶ Over.left (S1850P T) from Limits.coprod.inl) (by
    show Limits.coprod.inl ≫ Over.hom (S1850P T) = Over.hom T
    rw [show Over.hom (S1850P T) =
      Limits.coprod.desc (Over.hom T) (Over.hom T) from rfl]
    rw [Limits.coprod.inl_desc])

/-- The second inclusion `T ⟶ T ⨿ T`. -/
noncomputable def S1850Inr (T : SchemeOverField S1850F) : T ⟶ S1850P T :=
  Over.homMk (show Over.left T ⟶ Over.left (S1850P T) from Limits.coprod.inr) (by
    show Limits.coprod.inr ≫ Over.hom (S1850P T) = Over.hom T
    rw [show Over.hom (S1850P T) =
      Limits.coprod.desc (Over.hom T) (Over.hom T) from rfl]
    rw [Limits.coprod.inr_desc])

theorem S1850Inl_fold (T : SchemeOverField S1850F) :
    S1850Inl T ≫ S1850Fold T = 𝟙 T := by
  apply Comma.hom_ext
  · show Limits.coprod.inl ≫ Limits.coprod.desc (𝟙 T.left) (𝟙 T.left) = 𝟙 T.left
    rw [Limits.coprod.inl_desc]
  · apply Subsingleton.elim

theorem S1850Fold_left (T : SchemeOverField S1850F) :
    Over.Hom.left (S1850Fold T) =
      Limits.coprod.desc (𝟙 T.left) (𝟙 T.left) := rfl

theorem S1850Inl_left (T : SchemeOverField S1850F) :
    Over.Hom.left (S1850Inl T) = Limits.coprod.inl := rfl

theorem S1850Inr_left (T : SchemeOverField S1850F) :
    Over.Hom.left (S1850Inr T) = Limits.coprod.inr := rfl

theorem S1850P_left (T : SchemeOverField S1850F) :
    Over.left (S1850P T) = (Over.left T ⨿ Over.left T) := rfl

/-- The strong transformation induced by the fold. -/
noncomputable abbrev S1850FoldStrong (T : SchemeOverField S1850F) :
    Pseudofunctor.StrongTrans (S1743Y (S1850P T)) (S1743Y T) :=
  S1742StrongTransOfHom (F := S1850F) (S1850Fold T)

/-- The strong transformation induced by the first inclusion. -/
noncomputable abbrev S1850InlStrong (T : SchemeOverField S1850F) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743Y (S1850P T)) :=
  S1742StrongTransOfHom (F := S1850F) (S1850Inl T)

theorem S1850InlFold_eval (T : SchemeOverField S1850F) :
    S1743YonedaEval T T
      (Pseudofunctor.StrongTrans.vcomp (S1850InlStrong T) (S1850FoldStrong T)) = 𝟙 T := by
  rw [S1743YonedaEval_vcomp, S1743YonedaEval_eq_S1742, S1743YonedaEval_eq_S1742,
    S1742HomOfStrongTrans_strongTransOfHom,
    S1742HomOfStrongTrans_strongTransOfHom, S1850Inl_fold]

/-- The first inclusion splits the fold: `inl ≫ fold ≅ 𝟙` as a 2-isomorphism of
strong transformations. -/
theorem S1850InlFold_iso (T : SchemeOverField S1850F) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1850InlStrong T) (S1850FoldStrong T))
      (Pseudofunctor.StrongTrans.id (S1743Y T))) := by
  refine S1756IsoOfEvalEq T T _ _ ?_
  rw [S1850InlFold_eval, S1756YonedaEval_id]

/-- The representable map of the fold. -/
noncomputable def S1850FoldMap (T : SchemeOverField S1850F) :
    SchemeRepresentableMap (S1850Fold T) :=
  S1743SchemeRepresentableMap (S1850Fold T)

/-- The 2-isomorphism `(v ; inl) ; fold ≅ v` for an arbitrary cone leg `v`. -/
noncomputable def S1850ConeIsoY (T : SchemeOverField S1850F)
    {W : EtaleStackPseudofunctor S1850F} (v : Pseudofunctor.StrongTrans W (S1743Y T)) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp v (S1850InlStrong T)) (S1850FoldStrong T)) v :=
  (S1756AssociatorIso v (S1850InlStrong T) (S1850FoldStrong T)).trans
    ((S1756WhiskerLeftIso v _ _
        (Classical.choice (S1850InlFold_iso T))).trans
      (S1756RightUnitorIso v))

/-- The comparison 2-cell `liftToX` of the doubled square: the lift of a cone is
its second leg followed by the first inclusion. -/
noncomputable def S1850ConeIsoX (T : SchemeOverField S1850F)
    {W : EtaleStackPseudofunctor S1850F}
    (u : Pseudofunctor.StrongTrans W S1850X.fiber)
    (v : Pseudofunctor.StrongTrans W (S1743Y T))
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber)
    (comm : Iso (Pseudofunctor.StrongTrans.vcomp u
        (Pseudofunctor.StrongTrans.id S1850X.fiber))
      (Pseudofunctor.StrongTrans.vcomp v q)) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp v (S1850InlStrong T))
          (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q)) u :=
  (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp v (S1850InlStrong T))
      (S1850FoldStrong T) q).symm.trans
    ((S1756WhiskerRightIso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp v (S1850InlStrong T)) (S1850FoldStrong T))
        v q (S1850ConeIsoY T v)).trans
      (comm.symm.trans (S1756RightUnitorIso u)))

/-- The 2-commutative square of the doubled presentation:
`toSource ; map ≅ fold ; q`. -/
noncomputable def S1850Commutes (T : SchemeOverField S1850F)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q)
          (Pseudofunctor.StrongTrans.id S1850X.fiber))
      (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q) :=
  (S1756AssociatorIso (S1850FoldStrong T) q
      (Pseudofunctor.StrongTrans.id S1850X.fiber)).trans
    (S1756WhiskerLeftIso (S1850FoldStrong T) _ _
      (S1756RightUnitorIso q))

/-- The square of the uniform doubled presentation. -/
noncomputable def S1850Square (T : SchemeOverField S1850F)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    EtalePseudofunctorSquare (S1743Y (S1850P T)) S1850X.fiber (S1743Y T) S1850X.fiber :=
  EtalePseudofunctorSquare.mk
    (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q)
    (S1850FoldStrong T)
    (Pseudofunctor.StrongTrans.id S1850X.fiber) q (S1850Commutes T q)

/-- The weak two-pullback witness of the doubled square.  The lift of a cone is
its second leg followed by the first inclusion; the two comparison 2-cells are
built from the splitting `inl ; fold ≅ 𝟙` and the cone's own comparison; the
three coherence fields are equalities of modifications into representable
stacks, hence subsingletons. -/
noncomputable def S1850Witness (T : SchemeOverField S1850F)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    (S1850Square T q).TwoPullbackWitness where
  lift W cone :=
    Pseudofunctor.StrongTrans.vcomp cone.toY (S1850InlStrong T)
  liftToX W cone :=
    S1850ConeIsoX T cone.toX cone.toY q cone.commutes
  liftToY W cone :=
    S1850ConeIsoY T cone.toY
  liftTwoCell W source target morphism :=
    Pseudofunctor.StrongTrans.whiskerRight morphism.toY (S1850InlStrong T)
  liftTwoCell_toX := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp source.toY (S1850InlStrong T))
            (S1850Square T q).toX) ⟶
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp target.toY (S1850InlStrong T))
            (S1850Square T q).toX)) :=
      S1800Modification_subsingleton (S := S1726AffineOver) _ _
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp source.toY (S1850InlStrong T))
            (S1850Square T q).toY) ⟶
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp target.toY (S1850InlStrong T))
            (S1850Square T q).toY)) :=
      S1800Modification_subsingleton (S := T) _ _
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    haveI : Subsingleton (first ⟶ second) :=
      S1800Modification_subsingleton (S := S1850P T) _ _
    exact Subsingleton.elim _ _

/-- The uniform doubled base-change presentation of the identity map, at an
arbitrary test scheme and point.  Its projection is the fold `T ⨿ T ⟶ T`. -/
noncomputable def S1850Doubled (T : SchemeOverField S1850F)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    EtaleStackBaseChangePresentation
      (map := Pseudofunctor.StrongTrans.id S1850X.fiber) T q where
  pullbackScheme := S1850P T
  projection := S1850Fold T
  projectionMap := S1850FoldMap T
  toSource := Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q
  commutes := S1850Commutes T q
  isPullback := S1850Witness T q

/-! ## 2. The cover: finite etaleness and the doubled cover -/

/-- The doubled projection is finite. -/
theorem S1850Fold_finite (T : SchemeOverField S1850F) :
    IsFinite (Over.Hom.left (S1850Fold T)) := by
  change IsFinite (Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
  infer_instance

/-- The doubled projection is etale. -/
theorem S1850Fold_etale (T : SchemeOverField S1850F) :
    Etale (Over.Hom.left (S1850Fold T)) := by
  change Etale (Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
  let C := coprodOpenCover.{0, 0} (X := T.left) (Y := T.left)
  refine IsZariskiLocalAtSource.of_openCover C ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · change Etale (C.f (Sum.inl PUnit.unit) ≫
      Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
    simp only [C, coprodOpenCover, Sum.elim_inl]
    rw [Limits.coprod.inl_desc]
    infer_instance
  · change Etale (C.f (Sum.inr PUnit.unit) ≫
      Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
    simp only [C, coprodOpenCover, Sum.elim_inr]
    rw [Limits.coprod.inr_desc]
    infer_instance

theorem S1850Fold_finiteEtale (T : SchemeOverField S1850F) :
    IsFinite (Over.Hom.left (S1850Fold T)) ∧ Etale (Over.Hom.left (S1850Fold T)) :=
  ⟨S1850Fold_finite T, S1850Fold_etale T⟩

/-- The uniform doubled finite-etale structure on the identity map. -/
noncomputable def S1850DoubledFiniteEtale :
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.id S1850X.fiber) where
  baseChange T q := S1850Doubled T q
  hasProperty T q := S1850Fold_finiteEtale T

/-- The doubled-presentation cover.  Its source and map are those of the
terminal cover, but its identity-point presentation is doubled. -/
noncomputable def S1850DoubledCover : S1728Cover :=
  OrbicurveFiniteEtaleCover.mk S1850X
    (Pseudofunctor.StrongTrans.id S1850X.fiber) S1850DoubledFiniteEtale

theorem S1850Model :
    S1733Model S1850DoubledCover = S1850P S1850T := rfl

theorem S1850ModelOver :
    S1733ModelOver S1850DoubledCover = S1850Fold S1850T := rfl

theorem S1850SameSource :
    S1850DoubledCover.source = S1839TerminalCover.source := rfl

theorem S1850SameMap :
    HEq S1850DoubledCover.map S1839TerminalCover.map := HEq.rfl

/-! ## 3. The self-endomorphism is not the identity -/

/-- **The computation of the identity-point self-endomorphism**: for the doubled
presentation it is literally the composite `fold ; inl`.  This holds by
definitional reduction; no transport along an equality of models is involved. -/
theorem S1850End_direct :
    S1756End S1850DoubledCover = S1850Fold S1850T ≫ S1850Inl S1850T := rfl

/-- `fold ; inl` is not the identity of the doubled model: evaluating at the
second summand gives `inl x = inr x`, contradicting the disjointness of the
coproduct inclusions over the nonempty base `Spec R'`. -/
theorem S1850FoldInl_ne_id :
    (S1850Fold S1850T ≫ S1850Inl S1850T) ≠ 𝟙 (S1850P S1850T) := by
  intro h
  have hleft : Over.Hom.left (S1850Fold S1850T ≫ S1850Inl S1850T) =
      Over.Hom.left (𝟙 (S1850P S1850T)) := congrArg Over.Hom.left h
  rw [Over.comp_left, Over.id_left] at hleft
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  let x : S1850T.left := Classical.choice hne
  let y : (S1850P S1850T).left :=
    (Limits.coprod.inr : S1850T.left ⟶ (S1850P S1850T).left) x
  have hx := congrArg
    (fun f : (S1850P S1850T).left ⟶ (S1850P S1850T).left => f y) hleft
  change (Limits.coprod.desc (𝟙 S1850T.left) (𝟙 S1850T.left) ≫
      Limits.coprod.inl) y = (𝟙 ((S1850P S1850T).left)) y at hx
  rw [Scheme.Hom.comp_apply] at hx
  rw [show (Limits.coprod.desc (𝟙 S1850T.left) (𝟙 S1850T.left)) y =
      (Limits.coprod.inr ≫
        Limits.coprod.desc (𝟙 S1850T.left) (𝟙 S1850T.left)) x from rfl,
    Limits.coprod.inr_desc] at hx
  have hxid : ((𝟙 S1850T.left : S1850T.left ⟶ S1850T.left) x) = x := rfl
  have hy : y = (Limits.coprod.inr : S1850T.left ⟶ (S1850P S1850T).left) x := rfl
  rw [hxid, hy] at hx
  exact (AlgebraicGeometry.inl_ne_inr
    (X := S1850T.left) (Y := S1850T.left) x x) hx

/-- The identity-point self-endomorphism of the doubled cover is not the
identity. -/
theorem S1850End_ne :
    S1756End S1850DoubledCover ≠ 𝟙 (S1733Model S1850DoubledCover) := by
  intro h
  rw [S1850End_direct] at h
  exact S1850FoldInl_ne_id h

/-- **The refutation of S1756's first missing statement.** -/
theorem S1850_not_firstMissing : ¬ S1756FirstMissing :=
  fun h => S1850End_ne (h S1850DoubledCover)

/-! ## 4. Transport across the recorded equivalent models -/

/-- S1841's quasi-equivalence form is refuted as well. -/
theorem S1850_not_1841FirstMissing : ¬ S1841FirstMissing :=
  fun h => S1850_not_firstMissing ((S1841FirstMissing_iff_S1756).mp h)

/-- S1845's finite-etale-algebra endomorphism form is refuted. -/
theorem S1850_not_algEndTarget : ¬ S1845AlgEndTarget :=
  fun h => S1850_not_firstMissing
    ((S1845AlgEndTarget_iff_S1756FirstMissing).mp h)

/-- S1831's finite-etale-algebra form is refuted. -/
theorem S1850_not_1831AlgFirstMissing : ¬ S1831AlgFirstMissing :=
  fun h => S1850_not_algEndTarget
    ((S1845AlgEndTarget_iff_S1831AlgFirstMissing).mpr h)

/-- S1743's source retraction is refuted. -/
theorem S1850_not_sourceRetraction : ¬ S1743SourceRetraction :=
  fun h => S1850_not_firstMissing ((S1756Retraction_iff_firstMissing).mp h)

/-- The unit 2-cell itself fails for the doubled cover. -/
theorem S1850NoUnit : ¬ S1756Unit S1850DoubledCover :=
  fun h => S1850End_ne ((S1756Unit_iff_end S1850DoubledCover).mp h)

/-- No one-sided inverse of the comparison exists for the doubled cover. -/
theorem S1850NoRetraction :
    ¬ ∃ inv : Pseudofunctor.StrongTrans (S1743Source S1850DoubledCover)
        (S1743ModelStack S1850DoubledCover),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource S1850DoubledCover) inv)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack S1850DoubledCover))) :=
  fun h => S1850End_ne (S1756End_eq_one_of_retraction S1850DoubledCover h)

/-- The unit 2-cell holds for the terminal cover: the same source and map with
the canonical (identity) presentation. -/
theorem S1850TerminalUnit : S1756Unit S1839TerminalCover :=
  (S1756Unit_iff_end S1839TerminalCover).mpr S1845TerminalEnd

/-! ## 5. The presentation is not determined by the recorded witness -/

/-- The doubled projection is not an isomorphism. -/
theorem S1850Fold_not_iso : ¬ IsIso (S1850Fold S1850T) := by
  intro h
  have hsec : S1850Inl S1850T = inv (S1850Fold S1850T) := by
    calc
      S1850Inl S1850T = S1850Inl S1850T ≫ 𝟙 (S1850P S1850T) :=
        (Category.comp_id _).symm
      _ = S1850Inl S1850T ≫ (S1850Fold S1850T ≫ inv (S1850Fold S1850T)) := by
        rw [IsIso.hom_inv_id]
      _ = (S1850Inl S1850T ≫ S1850Fold S1850T) ≫ inv (S1850Fold S1850T) :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 S1850T ≫ inv (S1850Fold S1850T) := by rw [S1850Inl_fold]
      _ = inv (S1850Fold S1850T) := Category.id_comp _
  have hcomp : S1850Fold S1850T ≫ S1850Inl S1850T = 𝟙 (S1850P S1850T) := by
    rw [hsec, IsIso.hom_inv_id]
  exact S1850FoldInl_ne_id hcomp

theorem S1850TerminalProjection_eq :
    (S1839TerminalCover.finiteEtale.baseChange
      S1726AffineOver S1733BasePoint).projection = 𝟙 S1726AffineOver := rfl

theorem S1850DoubledProjection_eq :
    (S1850DoubledCover.finiteEtale.baseChange
      S1726AffineOver S1733BasePoint).projection = S1850Fold S1850T := rfl

/-- **Two presentations of the same map at the same point, not distinguished by
the recorded cover datum**: the canonical one has projection `𝟙` (an
isomorphism), the doubled one has projection `fold` (not an isomorphism).  Both
satisfy the recorded weak two-pullback witness, so the recorded datum does not
determine the identity-point presentation nor the self-endomorphism
`S1756End`. -/
theorem S1850Presentations_not_unique :
    IsIso ((S1839TerminalCover.finiteEtale.baseChange
        S1726AffineOver S1733BasePoint).projection) ∧
      ¬ IsIso ((S1850DoubledCover.finiteEtale.baseChange
        S1726AffineOver S1733BasePoint).projection) :=
  ⟨by rw [S1850TerminalProjection_eq]; exact IsIso.id S1726AffineOver, by
    rw [S1850DoubledProjection_eq]; exact S1850Fold_not_iso⟩

/-- **The same source and map give different self-endomorphisms**: the terminal
cover (canonical presentation) has identity self-endomorphism, while the
doubled presentation is `fold ; inl`. -/
theorem S1850SameSourceMap_differentEnd :
    S1756End S1839TerminalCover = 𝟙 (S1733Model S1839TerminalCover) ∧
      S1756End S1850DoubledCover ≠ 𝟙 (S1733Model S1850DoubledCover) :=
  ⟨S1845TerminalEnd, S1850End_ne⟩

/-! ## 6. Checks and audit -/

#check S1850Doubled
#check S1850Witness
#check S1850DoubledFiniteEtale
#check S1850DoubledCover
#check S1850SameSource
#check S1850SameMap
#check S1850End_direct
#check S1850FoldInl_ne_id
#check S1850End_ne
#check S1850_not_firstMissing
#check S1850_not_1841FirstMissing
#check S1850_not_algEndTarget
#check S1850_not_1831AlgFirstMissing
#check S1850_not_sourceRetraction
#check S1850NoUnit
#check S1850NoRetraction
#check S1850TerminalUnit
#check S1850Fold_not_iso
#check S1850Presentations_not_unique
#check S1850SameSourceMap_differentEnd

#print axioms S1850Inl_fold
#print axioms S1850InlFold_iso
#print axioms S1850Witness
#print axioms S1850Doubled
#print axioms S1850Fold_finiteEtale
#print axioms S1850DoubledCover
#print axioms S1850End_direct
#print axioms S1850FoldInl_ne_id
#print axioms S1850End_ne
#print axioms S1850_not_firstMissing
#print axioms S1850_not_1841FirstMissing
#print axioms S1850_not_algEndTarget
#print axioms S1850_not_1831AlgFirstMissing
#print axioms S1850_not_sourceRetraction
#print axioms S1850NoUnit
#print axioms S1850NoRetraction
#print axioms S1850TerminalUnit
#print axioms S1850Fold_not_iso
#print axioms S1850Presentations_not_unique
#print axioms S1850SameSourceMap_differentEnd

end LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
