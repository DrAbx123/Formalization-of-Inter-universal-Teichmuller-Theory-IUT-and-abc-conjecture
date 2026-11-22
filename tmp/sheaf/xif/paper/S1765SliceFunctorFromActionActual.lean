/-
# S1765: the slice functor from the S1744 action

## Question

S1744 constructed, for every actual cover map f : A --> B, a morphism
S1744ModelMapOfCoverMap A B f : S1733Model A --> S1733Model B, and asked for a
functor S1728Cover --> S1733Slice with object map S1744SliceObject and this
action on morphisms.

## Result

1. The action is well defined on the source 2-isomorphism quotient
   (S1765SliceMap_congr), so it descends to S1765Map on the homs of the
   actual category S1728ActualCategory11.

2. The action is functorial on composites (S1765Map_comp).

3. The action is faithful (S1765Map_injective), using the section
   lift vcomp toSource = id of S1743/S1756 and the 2-Yoneda comparison.

4. The action is NOT functorial on identities from the present data.  Its
   value on the identity class is the slice morphism induced by
   eval (toSource vcomp lift).  The identity law is equivalent to the missing
   unit 2-cell toSource vcomp lift = id, i.e. to S1756FirstMissing
   (equivalently S1743SourceRetraction): see S1765Map_id_iff_firstMissing.

5. Conditional on S1756FirstMissing, the functor exists:
   S1765FunctorOfFirstMissing : S1728Cover --> S1733Slice, with object map
   S1765Obj = S1744SliceObject and morphism map S1765Map.

6. The exact missing comparison statements:
   * full: S1765ActionSurjOnProjections, the R2b surjectivity restricted to
     model morphisms over Spec R'.  S1744's full R2b implies it
     (S1765ActionSurjOnProjections_of_R2b).  Not proved.
   * essentially surjective: S1765ObjectSurjective, the object-level
     surjectivity on the affine finite-etale slice.  Not proved.
   Faithfulness is proved.  The raw-injectivity statement R2a is not needed
   for faithfulness on the 2-iso quotient.

## Honest boundary

No sorry, no axiom, no Shrink/ULift/PUnit.  S1756FirstMissing is stated but
not inhabited.  The functor is constructed only from that hypothesis; the
file does not claim the hypothesis.  S1765ActionSurjOnProjections and
S1765ObjectSurjective are stated, not proved.
-/

import tmp.sheaf.xif.paper.S1744Category01AssemblyActual
import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1765SliceFunctorFromActionActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

local instance : Category.{1,1} S1728Cover := S1728ActualCategory11

attribute [local instance] S1744Model_isAffine

noncomputable abbrev S1765Y (S : SchemeOverField S1726K) :
    EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S

abbrev S1765Source (A : S1728Cover) : EtaleStackPseudofunctor S1726K :=
  A.source.fiber

noncomputable def S1765Eta (A B : S1728Cover) (f : S1728CoverMap A B) :
    Pseudofunctor.StrongTrans (S1765Y (S1733Model A)) (S1765Y (S1733Model B)) :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
    (S1743Lift B)

theorem S1765ModelMap_eq_eval (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1744ModelMapOfCoverMap A B f = S1742HomOfStrongTrans (S1765Eta A B f) := rfl

noncomputable def S1765LiftSection (A : S1728Cover) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1765Source A)) :=
  (S1743BaseChange A).isPullback.liftToX (S1765Source A) (S1743IdentityCone A)

noncomputable def S1765LiftProjection (A : S1728Cover) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A))
      A.map :=
  (S1743BaseChange A).isPullback.liftToY (S1765Source A) (S1743IdentityCone A)

theorem S1765Projection_eq (A : S1728Cover) :
    S1756Projection A = S1733ModelOver A := rfl

theorem S1765EvalProjection (A : S1728Cover) :
    S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) =
      S1733ModelOver A := by
  rw [S1756YonedaEval_projectionMap A, S1765Projection_eq A]

theorem S1765EvalId (S : SchemeOverField S1726K) :
    S1743YonedaEval S S
      (Pseudofunctor.StrongTrans.id (S1743Y S)) = 𝟙 S :=
  S1756YonedaEval_id S

noncomputable def S1765Step1 (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1765Eta A B f) (S1756ProjectionMap B))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1756ProjectionMap B))) :=
  S1756AssociatorIso
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
    (S1743Lift B) (S1756ProjectionMap B)

noncomputable def S1765Step2 (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1756ProjectionMap B)))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) B.map) :=
  S1756WhiskerLeftIso
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) _ _
    (S1765LiftProjection B)

noncomputable def S1765Step3 (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) B.map)
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp f.map B.map)) :=
  S1756AssociatorIso (S1756ToSource A) f.map B.map

noncomputable def S1765Step4 (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp f.map B.map))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) A.map) :=
  S1756WhiskerLeftIso (S1756ToSource A) _ _ f.commutes

noncomputable def S1765Step5 (A : S1728Cover) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) A.map)
      (Pseudofunctor.StrongTrans.vcomp (S1756ProjectionMap A) S1733BasePoint) :=
  (S1743BaseChange A).commutes

noncomputable def S1765Step6 (A : S1728Cover) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ProjectionMap A) S1733BasePoint)
      (S1756ProjectionMap A) :=
  S1756RightUnitorIso (S1756ProjectionMap A)

noncomputable def S1765EtaProjection (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1765Eta A B f) (S1756ProjectionMap B))
      (S1756ProjectionMap A) :=
  (S1765Step1 A B f).trans ((S1765Step2 A B f).trans ((S1765Step3 A B f).trans
    ((S1765Step4 A B f).trans ((S1765Step5 A).trans (S1765Step6 A)))))

theorem S1765ModelMap_over (A B : S1728Cover) (f : S1728CoverMap A B) :
    (S1744ModelMapOfCoverMap A B f).left ≫ (S1733ModelOver B).left =
      (S1733ModelOver A).left := by
  have hcomp := S1743YonedaEval_vcomp (S1733Model A) (S1733Model B)
    S1726AffineOver (S1765Eta A B f) (S1756ProjectionMap B)
  have hcongr : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp (S1765Eta A B f) (S1756ProjectionMap B)) =
      S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) :=
    S1742HomOfStrongTrans_congr (S1765EtaProjection A B f)
  have h : S1744ModelMapOfCoverMap A B f ≫ S1733ModelOver B = S1733ModelOver A := by
    calc
      S1744ModelMapOfCoverMap A B f ≫ S1733ModelOver B
          = S1743YonedaEval (S1733Model A) (S1733Model B) (S1765Eta A B f) ≫
              S1743YonedaEval (S1733Model B) S1726AffineOver (S1756ProjectionMap B) := by
            rw [S1765EvalProjection B]
            rfl
      _ = S1743YonedaEval (S1733Model A) S1726AffineOver
            (Pseudofunctor.StrongTrans.vcomp (S1765Eta A B f) (S1756ProjectionMap B)) := hcomp.symm
      _ = S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) := hcongr
      _ = S1733ModelOver A := S1765EvalProjection A
  exact congrArg Over.Hom.left h

abbrev S1765Obj (A : S1728Cover) : S1733Slice :=
  S1744SliceObject A

theorem S1765Obj_hom (A : S1728Cover) :
    (S1765Obj A).hom =
      (Scheme.isoSpec (S1733Model A).left).inv ≫ (S1733ModelOver A).left := rfl

theorem S1765Obj_left (A : S1728Cover) :
    (S1765Obj A).left =
      Opposite.op ((S1733Model A).left.presheaf.obj (Opposite.op ⊤)) := rfl

noncomputable def S1765SliceHom (A B : S1728Cover)
    (g : S1733Model A ⟶ S1733Model B)
    (hproj : g.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left) :
    S1765Obj A ⟶ S1765Obj B :=
  MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (f := (Scheme.Hom.appTop g.left).op)
    (by trivial) (by
      haveI hA : IsAffine (S1733Model A).left := S1744Model_isAffine A
      haveI hB : IsAffine (S1733Model B).left := S1744Model_isAffine B
      rw [S1765Obj_hom B, S1765Obj_hom A]
      show Spec.map (Scheme.Hom.appTop g.left) ≫
        ((Scheme.isoSpec (S1733Model B).left).inv ≫ (S1733ModelOver B).left) =
        ((Scheme.isoSpec (S1733Model A).left).inv ≫ (S1733ModelOver A).left)
      rw [← Category.assoc, Scheme.isoSpec_inv_naturality, Category.assoc, hproj])

noncomputable def S1765SliceMap (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1765Obj A ⟶ S1765Obj B :=
  S1765SliceHom A B (S1744ModelMapOfCoverMap A B f) (S1765ModelMap_over A B f)

theorem S1765SliceMap_congr (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : S1728CoverMapRel f g) : S1765SliceMap A B f = S1765SliceMap A B g := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  have hmodel : S1744ModelMapOfCoverMap A B f = S1744ModelMapOfCoverMap A B g := by
    apply S1742HomOfStrongTrans_congr
    exact S1756WhiskerRightIso _ _ (S1743Lift B)
      (S1756WhiskerLeftIso (S1756ToSource A) _ _ h.some)
  exact congrArg (fun m : S1733Model A ⟶ S1733Model B =>
    (Scheme.Hom.appTop (Over.Hom.left m)).op) hmodel

noncomputable def S1765Map (A B : S1728Cover) :
    (A ⟶ B) → (S1765Obj A ⟶ S1765Obj B) :=
  Quot.lift (fun f : S1728CoverMap A B => S1765SliceMap A B f)
    (fun f g h => S1765SliceMap_congr A B h)

theorem S1765Map_mk (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1765Map A B (Quot.mk _ f) = S1765SliceMap A B f := rfl

theorem S1765ModelMap_eq_evalY (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1744ModelMapOfCoverMap A B f =
      S1743YonedaEval (S1733Model A) (S1733Model B) (S1765Eta A B f) := rfl

theorem S1765SliceMap_left (A B : S1728Cover) (f : S1728CoverMap A B) :
    (S1765SliceMap A B f).left =
      (Scheme.Hom.appTop (Over.Hom.left (S1744ModelMapOfCoverMap A B f))).op := rfl

variable {P Q R S T U : EtaleStackPseudofunctor S1726K}

noncomputable def S1765CancelToMap
    (bA : Pseudofunctor.StrongTrans P Q) (lA : Pseudofunctor.StrongTrans Q P)
    (hA : Iso (Pseudofunctor.StrongTrans.vcomp lA bA)
      (Pseudofunctor.StrongTrans.id Q))
    (bB : Pseudofunctor.StrongTrans R S) (lB : Pseudofunctor.StrongTrans S R)
    (hB : Iso (Pseudofunctor.StrongTrans.vcomp lB bB)
      (Pseudofunctor.StrongTrans.id S))
    (f : Pseudofunctor.StrongTrans Q S) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp lA
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp bA f) lB)) bB)
      f :=
  (S1756AssociatorIso lA
    (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp bA f) lB) bB).trans
    ((S1756WhiskerLeftIso lA _ _
        (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp bA f) lB bB)).trans
      ((S1756WhiskerLeftIso lA _ _
          (S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp bA f) _ _ hB)).trans
        ((S1756WhiskerLeftIso lA _ _
            (S1756RightUnitorIso (Pseudofunctor.StrongTrans.vcomp bA f))).trans
          ((S1756AssociatorIso lA bA f).symm.trans
            ((S1756WhiskerRightIso _ _ f hA).trans
              (S1756LeftUnitorIso f))))))

noncomputable def S1765Compress
    (bA : Pseudofunctor.StrongTrans P Q) (f : Pseudofunctor.StrongTrans Q S)
    (lB : Pseudofunctor.StrongTrans S R) (bB : Pseudofunctor.StrongTrans R S)
    (g : Pseudofunctor.StrongTrans S T) (lC : Pseudofunctor.StrongTrans T U)
    (hB : Iso (Pseudofunctor.StrongTrans.vcomp lB bB)
      (Pseudofunctor.StrongTrans.id S)) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp bA f) lB)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp bB g) lC))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp bA
          (Pseudofunctor.StrongTrans.vcomp f g)) lC) :=
  (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp bA f) lB
    (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp bB g) lC)).trans
    ((S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp bA f) _ _
        (S1756AssociatorIso lB (Pseudofunctor.StrongTrans.vcomp bB g) lC).symm).trans
      ((S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp bA f) _ _
          (S1756WhiskerRightIso _ _ lC (S1756AssociatorIso lB bB g).symm)).trans
        ((S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp bA f) _ _
            (S1756WhiskerRightIso _ _ lC
              (S1756WhiskerRightIso _ _ g hB))).trans
          ((S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp bA f) _ _
              (S1756WhiskerRightIso _ _ lC (S1756LeftUnitorIso g))).trans
            ((S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp bA f) g lC).symm.trans
              (S1756WhiskerRightIso _ _ lC (S1756AssociatorIso bA f g)))))))

noncomputable def S1765Conj (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1765Eta A B f))
        (S1756ToSource B))
      f.map :=
  S1765CancelToMap (S1756ToSource A) (S1743Lift A) (S1765LiftSection A)
    (S1756ToSource B) (S1743Lift B) (S1765LiftSection B) f.map

noncomputable def S1765EtaComp (A B C : S1728Cover)
    (f : S1728CoverMap A B) (g : S1728CoverMap B C) :
    Iso
      (S1765Eta A C (S1641CoverMapComp f g))
      (Pseudofunctor.StrongTrans.vcomp (S1765Eta A B f) (S1765Eta B C g)) :=
  (S1765Compress (S1756ToSource A) f.map (S1743Lift B) (S1756ToSource B)
    g.map (S1743Lift C) (S1765LiftSection B)).symm

theorem S1765Map_comp (A B C : S1728Cover) (f : A ⟶ B) (g : B ⟶ C) :
    S1765Map A C (f ≫ g) = S1765Map A B f ≫ S1765Map B C g := by
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      change S1765Map A C (Quot.mk _ (S1641CoverMapComp f g)) =
        S1765Map A B (Quot.mk _ f) ≫ S1765Map B C (Quot.mk _ g)
      rw [S1765Map_mk, S1765Map_mk, S1765Map_mk]
      apply MorphismProperty.CostructuredArrow.Hom.ext
      have hmodel : S1744ModelMapOfCoverMap A C (S1641CoverMapComp f g) =
          S1744ModelMapOfCoverMap A B f ≫ S1744ModelMapOfCoverMap B C g := by
        calc
          S1744ModelMapOfCoverMap A C (S1641CoverMapComp f g)
              = S1743YonedaEval (S1733Model A) (S1733Model C)
                  (S1765Eta A C (S1641CoverMapComp f g)) :=
                S1765ModelMap_eq_evalY A C (S1641CoverMapComp f g)
          _ = S1743YonedaEval (S1733Model A) (S1733Model C)
                (Pseudofunctor.StrongTrans.vcomp (S1765Eta A B f) (S1765Eta B C g)) :=
              S1742HomOfStrongTrans_congr (S1765EtaComp A B C f g)
          _ = S1743YonedaEval (S1733Model A) (S1733Model B) (S1765Eta A B f) ≫
                S1743YonedaEval (S1733Model B) (S1733Model C) (S1765Eta B C g) :=
              S1743YonedaEval_vcomp (S1733Model A) (S1733Model B) (S1733Model C)
                (S1765Eta A B f) (S1765Eta B C g)
          _ = S1744ModelMapOfCoverMap A B f ≫ S1744ModelMapOfCoverMap B C g := by
              rw [← S1765ModelMap_eq_evalY, ← S1765ModelMap_eq_evalY]
      rw [MorphismProperty.Comma.comp_left]
      rw [S1765SliceMap_left, S1765SliceMap_left, S1765SliceMap_left]
      have happ := congrArg (fun m : S1733Model A ⟶ S1733Model C =>
        (Scheme.Hom.appTop (Over.Hom.left m)).op) hmodel
      rw [Over.comp_left, Scheme.Hom.comp_appTop, op_comp] at happ
      exact happ

theorem S1765SliceHom_injective {A B : S1728Cover}
    {g1 g2 : S1733Model A ⟶ S1733Model B}
    (h1 : g1.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left)
    (h2 : g2.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left)
    (h : S1765SliceHom A B g1 h1 = S1765SliceHom A B g2 h2) : g1 = g2 := by
  have hleft := congrArg (fun m : S1765Obj A ⟶ S1765Obj B => m.left) h
  have happ : (Over.Hom.left g1).appTop = (Over.Hom.left g2).appTop :=
    Quiver.Hom.op_inj hleft
  have hgl : Over.Hom.left g1 = Over.Hom.left g2 := AlgebraicGeometry.ext_of_isAffine happ
  exact Over.OverMorphism.ext hgl

theorem S1765Map_injective (A B : S1728Cover) :
    Function.Injective (S1765Map A B) := by
  intro q1 q2 h
  induction q1 using Quot.inductionOn with
  | h f =>
    induction q2 using Quot.inductionOn with
    | h g =>
      apply Quot.sound
      rw [S1765Map_mk, S1765Map_mk] at h
      have hleft := congrArg (fun m : S1765Obj A ⟶ S1765Obj B => m.left) h
      have happ : (S1744ModelMapOfCoverMap A B f).left.appTop =
          (S1744ModelMapOfCoverMap A B g).left.appTop :=
        Quiver.Hom.op_inj hleft
      have hgl : (S1744ModelMapOfCoverMap A B f).left =
          (S1744ModelMapOfCoverMap A B g).left := AlgebraicGeometry.ext_of_isAffine happ
      have hmodel : S1744ModelMapOfCoverMap A B f =
          S1744ModelMapOfCoverMap A B g := Over.OverMorphism.ext hgl
      have hEval : S1743YonedaEval (S1733Model A) (S1733Model B) (S1765Eta A B f) =
          S1743YonedaEval (S1733Model A) (S1733Model B) (S1765Eta A B g) := by
        rw [← S1765ModelMap_eq_evalY, ← S1765ModelMap_eq_evalY]
        exact hmodel
      have heta : Nonempty (S1765Eta A B f ≅ S1765Eta A B g) :=
        S1756IsoOfEvalEq (S1733Model A) (S1733Model B)
          (S1765Eta A B f) (S1765Eta A B g) hEval
      exact ⟨(S1765Conj A B f).symm.trans
        ((S1756WhiskerRightIso _ _ (S1756ToSource B)
          (S1756WhiskerLeftIso (S1743Lift A) _ _ heta.some)).trans
          (S1765Conj A B g))⟩

theorem S1765SliceHom_id (A : S1728Cover) :
    S1765SliceHom A A (𝟙 (S1733Model A)) (by simp) = 𝟙 (S1765Obj A) := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  show (Scheme.Hom.appTop (Over.Hom.left (𝟙 (S1733Model A)))).op = 𝟙 (S1765Obj A).left
  rw [Over.id_left, Scheme.Hom.id_appTop]
  rfl

theorem S1765Map_id_of_firstMissing (h : S1756FirstMissing) (A : S1728Cover) :
    S1765Map A A (𝟙 A) = 𝟙 (S1765Obj A) := by
  rw [show (𝟙 A) = Quot.mk _ (S1641CoverMapId A) from rfl, S1765Map_mk]
  have hEta : Iso (S1765Eta A A (S1641CoverMapId A))
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) :=
    (S1756WhiskerRightIso _ _ (S1743Lift A)
      (S1756RightUnitorIso (S1756ToSource A))).trans
      ((S1756Unit_iff_end A).mpr (h A)).some
  have hact : S1744ModelMapOfCoverMap A A (S1641CoverMapId A) = 𝟙 (S1733Model A) := by
    rw [S1765ModelMap_eq_evalY]
    have hi : S1743YonedaEval (S1733Model A) (S1733Model A)
          (S1765Eta A A (S1641CoverMapId A)) =
        S1743YonedaEval (S1733Model A) (S1733Model A)
          (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) :=
      S1742HomOfStrongTrans_congr hEta
    rw [hi]
    exact S1765EvalId (S1733Model A)
  apply MorphismProperty.CostructuredArrow.Hom.ext
  rw [S1765SliceMap_left]
  rw [hact, Over.id_left, Scheme.Hom.id_appTop]
  rfl

theorem S1765Map_id_iff_firstMissing :
    (∀ A : S1728Cover, S1765Map A A (𝟙 A) = 𝟙 (S1765Obj A)) ↔ S1756FirstMissing := by
  constructor
  · intro h A
    have hmap := h A
    rw [show (𝟙 A) = Quot.mk _ (S1641CoverMapId A) from rfl, S1765Map_mk] at hmap
    have hslice : S1765SliceHom A A
        (S1744ModelMapOfCoverMap A A (S1641CoverMapId A))
        (S1765ModelMap_over A A (S1641CoverMapId A)) = 𝟙 (S1765Obj A) := hmap
    have hslice' : S1765SliceHom A A
        (S1744ModelMapOfCoverMap A A (S1641CoverMapId A))
        (S1765ModelMap_over A A (S1641CoverMapId A)) =
        S1765SliceHom A A (𝟙 (S1733Model A)) (by simp) := by
      rw [hslice, S1765SliceHom_id]
    have hact : S1744ModelMapOfCoverMap A A (S1641CoverMapId A) = 𝟙 (S1733Model A) :=
      S1765SliceHom_injective _ _ hslice'
    have hEta : Iso (S1765Eta A A (S1641CoverMapId A))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) :=
      S1756WhiskerRightIso _ _ (S1743Lift A)
        (S1756RightUnitorIso (S1756ToSource A))
    have heval : S1743YonedaEval (S1733Model A) (S1733Model A)
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) =
          𝟙 (S1733Model A) := by
      have hi : S1743YonedaEval (S1733Model A) (S1733Model A)
            (S1765Eta A A (S1641CoverMapId A)) =
          S1743YonedaEval (S1733Model A) (S1733Model A)
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) :=
        S1742HomOfStrongTrans_congr hEta
      rw [← hi]
      rw [S1765ModelMap_eq_evalY] at hact
      exact hact
    simpa [S1756End] using heval
  · intro h A
    exact S1765Map_id_of_firstMissing h A

noncomputable def S1765FunctorOfFirstMissing (h : S1756FirstMissing) :
    S1728Cover ⥤ S1733Slice where
  obj := S1765Obj
  map := fun {A B} f => S1765Map A B f
  map_id := fun A => S1765Map_id_of_firstMissing h A
  map_comp := fun {A B C} f g => S1765Map_comp A B C f g

def S1765ActionSurjOnProjections : Prop :=
  ∀ (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B),
    g.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left →
      ∃ f : S1728CoverMap A B, S1744ModelMapOfCoverMap A B f = g

theorem S1765ActionSurjOnProjections_of_R2b
    (h : S1744CanonicalModelHomActionSurjective S1744CanonicalModelHomActionActual) :
    S1765ActionSurjOnProjections :=
  fun A B g _ => h A B g

def S1765ObjectSurjective : Prop :=
  ∀ S : S1733Slice, ∃ A : S1728Cover, Nonempty (S1765Obj A ≅ S)

theorem S1765EssSurj_iff (h : S1756FirstMissing) :
    (S1765FunctorOfFirstMissing h).EssSurj ↔ S1765ObjectSurjective := by
  constructor
  · intro hh S
    exact hh.mem_essImage S
  · intro hh
    exact ⟨hh⟩

theorem S1765FirstMissing_iff_map_id :
    S1756FirstMissing ↔ ∀ A : S1728Cover, S1765Map A A (𝟙 A) = 𝟙 (S1765Obj A) :=
  S1765Map_id_iff_firstMissing.symm

theorem S1765FirstMissing_iff_retraction :
    S1756FirstMissing ↔ S1743SourceRetraction :=
  S1756Retraction_iff_firstMissing.symm

#check S1765Conj
#check S1765EtaComp
#check S1765Map_comp
#check S1765SliceHom_injective
#check S1765Map_injective
#check S1765SliceHom_id
#check S1765Map_id_of_firstMissing
#check S1765Map_id_iff_firstMissing
#check S1765FunctorOfFirstMissing
#check S1765ActionSurjOnProjections
#check S1765ActionSurjOnProjections_of_R2b
#check S1765ObjectSurjective
#check S1765EssSurj_iff
#check S1765FirstMissing_iff_map_id
#check S1765FirstMissing_iff_retraction

#print axioms S1765Map_comp
#print axioms S1765Map_injective
#print axioms S1765Map_id_of_firstMissing
#print axioms S1765Map_id_iff_firstMissing
#print axioms S1765FunctorOfFirstMissing

end LeanFormal.IUT.XiFPaper.S1765SliceFunctorFromActionActual
