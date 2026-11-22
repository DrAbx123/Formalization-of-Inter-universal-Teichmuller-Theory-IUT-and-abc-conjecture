/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1812InverseModelHomActual
import tmp.sheaf.xif.paper.S1787StrictHomRealizationActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

/-!
# S1828: R1 / the S1755 hom equivalence, corrected to the slice over Spec R'

## The defect being corrected

S1755 states its missing hom comparison on *all* Over (Spec F') morphisms
between the affine models:

  S1755CoverModelHomEquivData A B : invFun : (Model A ⟶ Model B) → CoverMap A B,

and S1787 uses exactly this statement (S1755ModelHomEquivMissing) as the
hom-wise half of R1 for S1733ModelCategory, whose hom type is
Model A ⟶ Model B, i.e. Over (Spec F').

S1812 proved that this is *not* a geometric statement: every value of the
S1742/S1755 extraction lands in the slice

  S1812ModelHomOver A B = { g : Model A ⟶ Model B // g ≫ ModelOver B = ModelOver A },

and the Over triangle supplies this triangle only after post-composition with
the structure morphism Spec R' ⟶ Spec F', which is not a monomorphism
(S1812triangle_postcomp).  Consequently S1755ModelHomEquivMissing *forces every
model morphism to lie over Spec R'* (S1812ModelHomEquivMissing_implies_triangle):
it is strictly stronger than the geometric content.

## What this file does

1. It puts a genuine Category.{0,1} structure on the actual cover type whose
   homs are the slice homs S1812ModelHomOver (S1828ModelOverCategory).

2. It records the corrected hom-wise statement on the slice: from

   * S1755SourceRetraction  (the missing unit of the identity-point
     two-pullback, unchanged from S1755), and
   * S1766CoverMapDiscrete  (the honest discreteness residual: a
     2-isomorphism class of cover maps is a singleton),

   one gets the *raw* equivalence

     S1728CoverMap A B ≃ S1812ModelHomOver A B          (S1828SliceCoverEquiv)

   with toFun = S1812ModelHomOfCoverMapSlice and invFun =
   S1812ModelHomToCoverMap, the raw bijectivity S1828SliceBijective, and the
   compatibility with the 2-isomorphism quotient S1812QuotExtraction
   (S1828Quot_mk_apply, S1828QuotExtraction_bijective).

   The equivalence itself is S1812SliceEquiv, applied to the raw injectivity
   obtained from discreteness by S1812RawInjective_iff_discrete.  No new
   hypothesis is introduced here.

3. It proves the two functoriality inputs of R1 *on the slice*:

   * S1828ToCoverMap_id: the identity is sent to the identity up to
     2-isomorphism -- unconditional (it uses only the unconditional half
     S1755ModelSection of the two-pullback unit and
     S1742StrongTransOfHom 𝟙 ≅ 𝟙);
   * S1828ToCoverMap_comp: composition is respected up to 2-isomorphism --
     this uses S1755SourceRetraction at exactly one place, to cancel
     toSource ≫ ModelSectionLift.

   Consequently S1787's hypothesis S1787LiftFunctorial is *not* needed: the
   functoriality of the extraction was only needed there because the inverse of
   the bijection was obtained by Classical.choice.  Here the inverse is the
   explicit S1812 construction, for which the two laws are genuine proofs.

4. Hence R1 for the *slice* model category,

     S1828R1 : S1754S1726StrictRealizationMissing S1828ModelOverCategory,

   from S1755SourceRetraction and S1766CoverMapDiscrete alone
   (S1828StrictHomEquiv, S1828R1).

5. It records exactly what has to be rewritten in the S1787/S1754 targets.
   The S1787 target is R1 for S1733ModelCategory, i.e. for the hom type
   Model A ⟶ Model B:

   * S1828SliceFillsOver is the extra statement "every model morphism is a
     morphism over Spec R'".
   * S1828R1ModelCategory derives the S1787/S1754 target from
     S1755SourceRetraction, S1766CoverMapDiscrete and S1828SliceFillsOver.
   * S1828ModelHomEquivMissing_iff identifies the uncorrected hypothesis with
     S1828SliceFillsOver and S1766CoverMapDiscrete, i.e. the S1787 hypothesis is
     the slice statement plus the filling condition.
   * S1828CoverModelHomEquivData_filling shows that the S1755 inverse data on
     the full Over hom type itself forces the filling condition, so it cannot be
     obtained from the slice equivalence.

6. It transports the slice equivalence to the S1728/S1733 smallness chain: the
   slice hom type *is* a Type 0 carrier for the actual cover maps
   (S1828SmallRawCoverData), which gives the S1728 small raw cover data
   (S1828SmallRawCoverDataRequired) and an actual Category.{0,1} on the cover
   type (S1828CoverCategory01) without any Shrink/ULift.  S1733's
   S1733AffineCoverModel is recovered from this data plus the filling condition
   (S1828AffineCoverModelOfSlice), which exhibits the filling condition as the
   exact gap between S1733's target and the slice comparison.

## Honest boundary

No sorry, no axiom, no Shrink, no ULift, no PUnit.  The slice results are
conditional exactly on S1755SourceRetraction (used for the round trip and for
composition) and on S1766CoverMapDiscrete (used for raw injectivity).  Both are
recorded, not asserted.  The uncorrected S1787 hypothesis
S1755ModelHomEquivMissing is *not* claimed and is strictly stronger than the
slice statement.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1828SliceR1Actual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
open LeanFormal.IUT.XiFPaper.S1787StrictHomRealizationActual
open LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual

/-! ## 1. The slice model category on the actual cover type -/

/-- The identity of the slice: the identity model morphism, which is over the
base. -/
@[reducible] noncomputable def S1828SliceId (A : S1728Cover) : S1812ModelHomOver A A :=
  ⟨𝟙 (S1733Model A), Category.id_comp _⟩

/-- Composition of slice morphisms: the two triangles compose. -/
@[reducible] noncomputable def S1828SliceComp {A B C : S1728Cover}
    (f : S1812ModelHomOver A B) (g : S1812ModelHomOver B C) : S1812ModelHomOver A C :=
  ⟨f.1 ≫ g.1, by rw [Category.assoc, g.2, f.2]⟩

/-- The 1-cell underlying the S1812 inverse construction S1812ModelHomToCoverMap,
written out.  Keeping it as a separate definition keeps the statements of the
2-isomorphism lemmas small. -/
@[reducible] noncomputable def S1828ToCoverMapHom {A B : S1728Cover}
    (g : S1812ModelHomOver A B) : S1755Source A ⟶ S1755Source B :=
  ((S1755ModelSectionLift A).vcomp
    (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
      (T := S1733Model B) g.1)).vcomp (S1755BaseChange B).toSource

/-- The underlying 1-cell of S1812ModelHomToCoverMap is S1828ToCoverMapHom. -/
theorem S1828ToCoverMap_map {A B : S1728Cover} (g : S1812ModelHomOver A B) :
    (S1812ModelHomToCoverMap A B g).map = S1828ToCoverMapHom g := rfl

/-- The S1812 inverse construction, with its S1728CoverMap structure made
explicit so that its underlying 1-cell is definitionally S1828ToCoverMapHom.
This is the same cover map as S1812ModelHomToCoverMap (S1828CoverMapOfSlice_eq). -/
@[reducible] noncomputable def S1828CoverMapOfSlice {A B : S1728Cover}
    (g : S1812ModelHomOver A B) : S1728CoverMap A B where
  map := S1828ToCoverMapHom g
  commutes := (S1812ModelHomToCoverMap A B g).commutes

/-- S1828CoverMapOfSlice is the S1812 inverse construction. -/
theorem S1828CoverMapOfSlice_eq {A B : S1728Cover} (g : S1812ModelHomOver A B) :
    S1828CoverMapOfSlice g = S1812ModelHomToCoverMap A B g := rfl

/-- **The corrected model category.**  Its hom type from A to B is the *slice*
hom S1812ModelHomOver A B, i.e. a model morphism over Spec R', not the whole
Over (Spec F') hom type of S1733ModelCategory.  This is the hom type on which
the S1742/S1755 extraction has an inverse (S1812). -/
@[reducible] noncomputable def S1828ModelOverCategory : Category.{0, 1} S1728Cover where
  Hom A B := S1812ModelHomOver A B
  id A := S1828SliceId A
  comp f g := S1828SliceComp f g
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- The universe bookkeeping: the slice model category is a genuine
Category.{0,1} on the actual cover type, as demanded by the target. -/
example : Category.{0, 1} S1728Cover := S1828ModelOverCategory

/-- The identity of the slice model category is the identity model morphism. -/
@[simp] theorem S1828ModelOverCategory_id_val (A : S1728Cover) :
    (S1828SliceId A).1 = 𝟙 (S1733Model A) := rfl

/-- Composition in the slice model category is composition of the underlying
model morphisms. -/
@[simp] theorem S1828ModelOverCategory_comp_val {A B C : S1728Cover}
    (f : S1812ModelHomOver A B) (g : S1812ModelHomOver B C) :
    (S1828SliceComp f g).1 = f.1 ≫ g.1 := rfl

/-- The category composition is the explicit slice composition. -/
theorem S1828ModelOverCategory_comp_eq {A B C : S1728Cover}
    (f : S1812ModelHomOver A B) (g : S1812ModelHomOver B C) :
    @CategoryStruct.comp S1728Cover S1828ModelOverCategory.toCategoryStruct A B C f g =
      S1828SliceComp f g := rfl

/-- The category identity is the explicit slice identity. -/
theorem S1828ModelOverCategory_id_eq (A : S1728Cover) :
    @CategoryStruct.id S1728Cover S1828ModelOverCategory.toCategoryStruct A = S1828SliceId A :=
  rfl

/-! ## 2. The corrected hom-wise statement on the slice -/

/-- **Raw injectivity on the slice from discreteness.**  This is exactly
S1812's dictionary S1812RawInjective_iff_discrete. -/
theorem S1828RawInjective (hd : S1766CoverMapDiscrete) :
    ∀ A B : S1728Cover, S1812RawInjective A B :=
  S1812RawInjective_iff_discrete.mpr hd

/-- **The corrected hom comparison**: the actual cover maps are equivalent to
the *slice* hom type of the affine models, with the extraction as forward map
and the S1812 construction as inverse. -/
noncomputable def S1828SliceCoverEquiv (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : S1728Cover) :
    S1728CoverMap A B ≃ S1812ModelHomOver A B :=
  S1812SliceEquiv h (S1828RawInjective hd) A B

/-- Computation rule: the forward map of the corrected equivalence is the
extraction. -/
theorem S1828SliceCoverEquiv_apply (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1828SliceCoverEquiv h hd A B f = S1812ModelHomOfCoverMapSlice A B f := rfl

/-- Computation rule: the inverse of the corrected equivalence is the S1812
construction S1812ModelHomToCoverMap. -/
theorem S1828SliceCoverEquiv_symm_apply (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : S1728Cover) (g : S1812ModelHomOver A B) :
    (S1828SliceCoverEquiv h hd A B).symm g = S1812ModelHomToCoverMap A B g := rfl

/-- **Raw bijectivity on the slice** from S1755SourceRetraction and
S1766CoverMapDiscrete. -/
theorem S1828SliceBijective (h : S1755SourceRetraction) (hd : S1766CoverMapDiscrete)
    (A B : S1728Cover) : Function.Bijective (S1812ModelHomOfCoverMapSlice A B) :=
  (S1828SliceCoverEquiv h hd A B).bijective

/-- The raw bijectivity is exactly S1812's slice bijectivity, itself equivalent
to raw injectivity of the extraction (S1812SliceBijective_iff). -/
theorem S1828SliceBijective_iff (h : S1755SourceRetraction) (A B : S1728Cover) :
    Function.Bijective (S1812ModelHomOfCoverMapSlice A B) ↔ S1812RawInjective A B :=
  S1812SliceBijective_iff h A B

/-- The 2-isomorphism quotient version is unconditional given
S1755SourceRetraction; it does not need discreteness. -/
theorem S1828QuotExtraction_bijective (h : S1755SourceRetraction) (A B : S1728Cover) :
    Function.Bijective (S1812QuotExtraction A B) :=
  S1812QuotExtraction_bijective h A B

/-- **Descent**: the quotient bijection is the descent of the raw equivalence
along the quotient map. -/
theorem S1828Quot_mk_apply (h : S1755SourceRetraction) (hd : S1766CoverMapDiscrete)
    (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1812QuotExtraction A B (Quot.mk _ f) = S1828SliceCoverEquiv h hd A B f := rfl

/-- The quotient bijection is injective. -/
theorem S1828QuotExtraction_injective (h : S1755SourceRetraction) (A B : S1728Cover) :
    Function.Injective (S1812QuotExtraction A B) :=
  (S1812QuotExtraction_bijective h A B).1

/-- The quotient bijection is surjective. -/
theorem S1828QuotExtraction_surjective (h : S1755SourceRetraction) (A B : S1728Cover) :
    Function.Surjective (S1812QuotExtraction A B) :=
  (S1812QuotExtraction_bijective h A B).2

/-- The filling condition: every Over (Spec F') morphism between the affine
models is in fact a morphism over Spec R'.  This is precisely the extra datum
that the S1755/S1787 statement on all Over homomorphisms silently assumes. -/
def S1828SliceFillsOver : Prop :=
  ∀ (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B),
    g ≫ S1733ModelOver B = S1733ModelOver A

/-- **The uncorrected statement is the slice statement plus filling.**  Under
S1755SourceRetraction, the S1755/S1787 hypothesis on *all* Over (Spec F')
morphisms is equivalent to: every model morphism is over Spec R' (the filling
condition) together with discreteness of the cover-map hom types.  This is the
precise sense in which the S1787 hypothesis has to be rewritten. -/
theorem S1828ModelHomEquivMissing_iff (h : S1755SourceRetraction) :
    S1755ModelHomEquivMissing ↔ (S1828SliceFillsOver ∧ S1766CoverMapDiscrete) := by
  constructor
  · intro hm
    obtain ⟨htri, hraw⟩ := (S1812ModelHomEquivMissing_iff h).mp hm
    exact ⟨htri, S1812RawInjective_iff_discrete.mp hraw⟩
  · rintro ⟨htri, hd⟩
    exact (S1812ModelHomEquivMissing_iff h).mpr
      ⟨htri, S1812RawInjective_iff_discrete.mpr hd⟩

/-- The S1755 inverse data on the *full* Over hom type forces the filling
condition, for that single pair of covers.  So it cannot be produced from the
slice equivalence alone: the missing input is not the inverse but the filling
of the slice. -/
theorem S1828CoverModelHomEquivData_filling {A B : S1728Cover}
    (d : S1755CoverModelHomEquivData A B) :
    ∀ g : S1733Model A ⟶ S1733Model B, g ≫ S1733ModelOver B = S1733ModelOver A := by
  intro g
  have h1 : S1755ModelHomOfCoverMap A B (d.invFun g) = g := d.right_inv g
  calc g ≫ S1733ModelOver B
      = S1755ModelHomOfCoverMap A B (d.invFun g) ≫ S1733ModelOver B := by rw [h1]
    _ = S1733ModelOver A := S1812ModelHomOfCoverMap_triangle A B (d.invFun g)

/-- Consequently the S1755 hom equivalence data forces the slice to be the
whole Over hom type. -/
theorem S1828ModelHomEquivMissing_filling (h : S1755ModelHomEquivMissing) :
    S1828SliceFillsOver :=
  S1812ModelHomEquivMissing_implies_triangle h

/-- The uncorrected S1787 hypothesis, obtained from the slice hypotheses and the
filling condition.  This is the bridge to S1787's formulation. -/
theorem S1828ModelHomEquivMissing_of_slice (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (htri : S1828SliceFillsOver) :
    S1755ModelHomEquivMissing :=
  (S1828ModelHomEquivMissing_iff h).mpr ⟨htri, hd⟩

/-- S1787's packaged hypothesis S1787FirstMissing, obtained from the slice
hypotheses, the filling condition and S1787's functoriality input. -/
theorem S1828S1787FirstMissing_of_slice (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (htri : S1828SliceFillsOver)
    (hfun : S1787LiftFunctorial) : S1787FirstMissing :=
  ⟨S1828ModelHomEquivMissing_of_slice h hd htri, hfun⟩

/-! ## 3. The extraction of the identity is the identity -/

/-- The strong transformation induced by the identity scheme morphism is
2-isomorphic to the identity strong transformation. -/
noncomputable def S1828StrongTransOfHom_id (S : SchemeOverField S1726K) :
    Iso (S1742StrongTransOfHom (F := S1726K) (𝟙 S))
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S)) :=
  S1755IsoOfEvalEq _ _ (by
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    rfl)

/-- **The identity cover map is sent to the identity model morphism, up to
2-isomorphism.**  This is unconditional: it uses only the unconditional half
S1755ModelSection of the two-pullback unit. -/
noncomputable def S1828ToCoverMap_id (A : S1728Cover) :
    Iso (S1828ToCoverMapHom (S1828SliceId A))
      (Pseudofunctor.StrongTrans.id (S1755Source A)) := by
  let sec : S1755Source A ⟶ S1755ModelStack A := S1755ModelSectionLift A
  let a : S1755ModelStack A ⟶ S1755Source A := (S1755BaseChange A).toSource
  let ST : S1755ModelStack A ⟶ S1755ModelStack A :=
    S1742StrongTransOfHom (F := S1726K) (𝟙 (S1733Model A))
  have hST : Iso ST (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) :=
    S1828StrongTransOfHom_id _
  have h1 : Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp sec ST) a)
      (Pseudofunctor.StrongTrans.vcomp sec (Pseudofunctor.StrongTrans.vcomp ST a)) :=
    S1756AssociatorIso sec ST a
  have h2 : Iso (Pseudofunctor.StrongTrans.vcomp sec (Pseudofunctor.StrongTrans.vcomp ST a))
      (Pseudofunctor.StrongTrans.vcomp sec
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) a)) :=
    S1756WhiskerLeftIso sec (Pseudofunctor.StrongTrans.vcomp ST a)
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) a)
      (S1756WhiskerRightIso ST (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) a hST)
  have h3 : Iso (Pseudofunctor.StrongTrans.vcomp sec
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) a))
      (Pseudofunctor.StrongTrans.vcomp sec a) :=
    S1756WhiskerLeftIso sec
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) a) a
      (S1756LeftUnitorIso a)
  have h4 : Iso (Pseudofunctor.StrongTrans.vcomp sec a)
      (Pseudofunctor.StrongTrans.id (S1755Source A)) := S1755ModelSection A
  exact h1.trans (h2.trans (h3.trans h4))

/-! ## 4. Composition is respected up to 2-isomorphism -/

/-- **The inverse construction is compatible with composition, up to
2-isomorphism.**  The only place where the missing unit of the two-pullback is
used is the cancellation of toSource ≫ ModelSectionLift (S1755SourceRetraction);
the rest is the functoriality of S1742StrongTransOfHom and associativity in the
bicategory. -/
noncomputable def S1828ToCoverMap_comp (h : S1755SourceRetraction) {A B C : S1728Cover}
    (f : S1812ModelHomOver A B) (g : S1812ModelHomOver B C) :
    Iso (S1828ToCoverMapHom (S1828SliceComp f g))
      (Pseudofunctor.StrongTrans.vcomp
        (S1828ToCoverMapHom f) (S1828ToCoverMapHom g)) := by
  let secA : S1755Source A ⟶ S1755ModelStack A := S1755ModelSectionLift A
  let secB : S1755Source B ⟶ S1755ModelStack B := S1755ModelSectionLift B
  let aB : S1755ModelStack B ⟶ S1755Source B := (S1755BaseChange B).toSource
  let aC : S1755ModelStack C ⟶ S1755Source C := (S1755BaseChange C).toSource
  let STf : S1755ModelStack A ⟶ S1755ModelStack B :=
    S1742StrongTransOfHom (F := S1726K) f.1
  let STg : S1755ModelStack B ⟶ S1755ModelStack C :=
    S1742StrongTransOfHom (F := S1726K) g.1
  let STfg : S1755ModelStack A ⟶ S1755ModelStack C :=
    S1742StrongTransOfHom (F := S1726K) (f.1 ≫ g.1)
  have hST : Iso STfg (Pseudofunctor.StrongTrans.vcomp STf STg) :=
    (S1755StrongTransOfHomIsoComp f.1 g.1).symm
  have hRetr : Iso (Pseudofunctor.StrongTrans.vcomp aB secB)
      (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) :=
    (S1755ModelSection_retraction h B).some
  -- the left-hand side, normalized to (secA ≫ STf) ≫ (STg ≫ aC)
  have e1 : Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STfg) aC)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp secA (Pseudofunctor.StrongTrans.vcomp STf STg)) aC) :=
    S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp secA STfg)
      (Pseudofunctor.StrongTrans.vcomp secA (Pseudofunctor.StrongTrans.vcomp STf STg)) aC
      (S1756WhiskerLeftIso secA STfg (Pseudofunctor.StrongTrans.vcomp STf STg) hST)
  have e2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp secA (Pseudofunctor.StrongTrans.vcomp STf STg)) aC)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf) STg) aC) :=
    S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp secA (Pseudofunctor.StrongTrans.vcomp STf STg))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf) STg) aC
      (S1756AssociatorIso secA STf STg).symm
  have e3 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf) STg) aC)
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp STg aC)) :=
    S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp secA STf) STg aC
  -- the right-hand side, normalized to the same
  have f1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf) aB)
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secB STg) aC))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp aB
          (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secB STg) aC))) :=
    S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp secA STf) aB
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secB STg) aC)
  have f2 : Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp aB
          (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secB STg) aC)))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp aB
          (Pseudofunctor.StrongTrans.vcomp secB (Pseudofunctor.StrongTrans.vcomp STg aC)))) :=
    S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp secA STf)
      (Pseudofunctor.StrongTrans.vcomp aB
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secB STg) aC))
      (Pseudofunctor.StrongTrans.vcomp aB
        (Pseudofunctor.StrongTrans.vcomp secB (Pseudofunctor.StrongTrans.vcomp STg aC)))
      (S1756WhiskerLeftIso aB (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secB STg) aC)
        (Pseudofunctor.StrongTrans.vcomp secB (Pseudofunctor.StrongTrans.vcomp STg aC))
        (S1756AssociatorIso secB STg aC))
  have f3 : Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp aB
          (Pseudofunctor.StrongTrans.vcomp secB (Pseudofunctor.StrongTrans.vcomp STg aC))))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp aB secB) STg) aC)) :=
    S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp secA STf)
      (Pseudofunctor.StrongTrans.vcomp aB
        (Pseudofunctor.StrongTrans.vcomp secB (Pseudofunctor.StrongTrans.vcomp STg aC)))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp aB secB) STg) aC)
      ((S1756AssociatorIso aB secB (Pseudofunctor.StrongTrans.vcomp STg aC)).symm.trans
        (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp aB secB) STg aC).symm)
  have f4 : Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp aB secB) STg) aC))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg) aC)) :=
    S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp secA STf)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp aB secB) STg) aC)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg) aC)
      (S1756WhiskerRightIso
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp aB secB) STg)
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg) aC
        (S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp aB secB)
          (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg hRetr))
  have f5 : Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg) aC))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp secA STf)
        (Pseudofunctor.StrongTrans.vcomp STg aC)) :=
    S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp secA STf)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg) aC)
      (Pseudofunctor.StrongTrans.vcomp STg aC)
      (S1756WhiskerRightIso
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) STg)
        STg aC (S1756LeftUnitorIso STg))
  exact (e1.trans (e2.trans e3)).trans (f1.trans (f2.trans (f3.trans (f4.trans f5)))).symm

/-! ## 5. R1 for the slice, and its comparison with the S1787 target -/

/-- The inverse of the extraction as an equivalence into the actual cover maps. -/
noncomputable def S1828SliceHomEquiv (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : S1728Cover) :
    S1812ModelHomOver A B ≃ S1728CoverMap A B where
  toFun := S1828CoverMapOfSlice
  invFun := S1812ModelHomOfCoverMapSlice A B
  left_inv g := by
    rw [S1828CoverMapOfSlice_eq]
    exact Subtype.ext (S1812ModelHomOfCoverMap_toCoverMap h A B g)
  right_inv f := by
    rw [S1828CoverMapOfSlice_eq]
    exact S1812LeftInverse_of_rawInjective h (S1828RawInjective hd) A B f

/-- S1828SliceHomEquiv is the inverse of S1828SliceCoverEquiv, up to the
definitional identification of S1828CoverMapOfSlice with the S1812 construction. -/
theorem S1828SliceHomEquiv_apply (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : S1728Cover) (g : S1812ModelHomOver A B) :
    S1828SliceHomEquiv h hd A B g = S1812ModelHomToCoverMap A B g :=
  S1828CoverMapOfSlice_eq g

/-- **The hom-wise comparison of R1, on the slice.**  R1's equiv field is the
inverse of the S1812 extraction; the two compatibility laws are
S1828ToCoverMap_id and S1828ToCoverMap_comp.  Note that no functoriality of the
S1755 lift (S1787LiftFunctorial) is needed. -/
noncomputable def S1828StrictHomEquiv (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) :
    @S1754StrictHomEquiv S1726K _ S1726Orbicurve S1828ModelOverCategory := by
  letI := S1828ModelOverCategory
  exact
    { equiv := fun A B => S1828SliceHomEquiv h hd A B
      id_compat := fun A => S1828ToCoverMap_id A
      comp_compat := fun f g => S1828ToCoverMap_comp h f g }

/-- **R1, corrected: the target is the slice model category.**  From the two
recorded hypotheses (the missing unit of the two-pullback and discreteness of
cover-map hom types) the five categorical fields hold for the slice homs. -/
theorem S1828R1 (h : S1755SourceRetraction) (hd : S1766CoverMapDiscrete) :
    S1754S1726StrictRealizationMissing S1828ModelOverCategory := by
  letI := S1828ModelOverCategory
  exact ⟨S1828StrictHomEquiv h hd⟩

/-- The filling condition transports the slice comparison to the full Over hom
type: the subtype projection is an equivalence when every model morphism is in
the slice. -/
noncomputable def S1828OverToSlice (htri : S1828SliceFillsOver) (A B : S1728Cover) :
    (S1733Model A ⟶ S1733Model B) ≃ S1812ModelHomOver A B where
  toFun g := ⟨g, htri A B g⟩
  invFun g := g.1
  left_inv g := rfl
  right_inv g := Subtype.ext rfl

/-- **R1 for S1733ModelCategory**, the S1787 target, from the slice hypotheses
and the filling condition.  The only difference from S1828R1 is the transport of
the hom type along S1828OverToSlice. -/
noncomputable def S1828StrictHomEquivOfSlice (htri : S1828SliceFillsOver)
    (h : S1755SourceRetraction) (hd : S1766CoverMapDiscrete) :
    @S1754StrictHomEquiv S1726K _ S1726Orbicurve S1733ModelCategory := by
  letI := S1733ModelCategory
  exact
    { equiv := fun A B => (S1828OverToSlice htri A B).trans (S1828SliceHomEquiv h hd A B)
      id_compat := fun A => S1828ToCoverMap_id A
      comp_compat := fun f g =>
        S1828ToCoverMap_comp h ⟨f, htri _ _ f⟩ ⟨g, htri _ _ g⟩ }

/-- **R1 for the uncorrected S1787/S1754 target.**  From the two recorded
hypotheses and the filling condition. -/
theorem S1828R1ModelCategory (h : S1755SourceRetraction) (hd : S1766CoverMapDiscrete)
    (htri : S1828SliceFillsOver) :
    S1754S1726StrictRealizationMissing S1733ModelCategory := by
  letI := S1733ModelCategory
  exact ⟨S1828StrictHomEquivOfSlice htri h hd⟩

/-! ## 6. The smallness chain: the slice homs as a small carrier -/

/-- **The slice hom type is a Type 0 carrier for the actual cover maps.**  This
is the corrected form of S1733AffineCoverModel.homEquiv: the hom comparison has
to be taken on the slice, not on the whole Over hom type. -/
noncomputable def S1828SmallRawCoverData (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) (A B : S1728Cover) :
    S1728ActualSmallRawCoverData A B where
  Carrier := S1812ModelHomOver A B
  equiv := S1828SliceHomEquiv h hd A B

/-- Consequently the S1728 small raw cover data hold. -/
theorem S1828SmallRawCoverDataRequired (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) : S1728SmallRawCoverDataRequired :=
  fun A B => ⟨S1828SmallRawCoverData h hd A B⟩

/-- Consequently the actual cover type carries a genuine Category.{0,1} (the
S1728 construction from small raw cover data), with no Shrink or ULift. -/
@[reducible] noncomputable def S1828CoverCategory01 (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) : Category.{0, 1} S1728Cover :=
  S1728ActualCategory01 (fun A B => S1812ModelHomOver A B)
    (fun A B => S1828SliceHomEquiv h hd A B)

/-- The slice version of S1733AffineCoverModelMissing: a Type 0 carrier for the
actual cover maps on every pair, with the S1733 model fixed. -/
def S1828SliceAffineCoverModelMissing : Prop :=
  ∀ A B : S1728Cover, Nonempty (S1812ModelHomOver A B ≃ S1728CoverMap A B)

/-- The slice version of S1733's missing affine cover model holds from the two
recorded hypotheses. -/
theorem S1828SliceAffineCoverModelMissing_holds (h : S1755SourceRetraction)
    (hd : S1766CoverMapDiscrete) : S1828SliceAffineCoverModelMissing :=
  fun A B => ⟨S1828SliceHomEquiv h hd A B⟩

/-- **S1733's S1733AffineCoverModel from the slice data plus filling.**  The
filling condition is exactly the extra input that S1733's homEquiv on the full
Over hom type requires. -/
noncomputable def S1828AffineCoverModelOfSlice (htri : S1828SliceFillsOver)
    (hM : S1828SliceAffineCoverModelMissing) : S1733AffineCoverModel where
  model := S1733Model
  toBase := S1733ModelOver
  isAffine := S1755Model_isAffine
  isFinite A := (S1733Model_finiteEtale A).1
  isEtale A := (S1733Model_finiteEtale A).2
  homEquiv A B := (S1828OverToSlice htri A B).trans (Classical.choice (hM A B))

/-- S1733's first missing theorem, from the slice data and the filling
condition. -/
theorem S1828AffineCoverModelMissing_of_slice (htri : S1828SliceFillsOver)
    (hM : S1828SliceAffineCoverModelMissing) : S1733AffineCoverModelMissing :=
  ⟨S1828AffineCoverModelOfSlice htri hM⟩

/-! ## 7. Checks -/

#check S1828ModelOverCategory
#check S1828RawInjective
#check S1828SliceCoverEquiv
#check S1828SliceBijective
#check S1828QuotExtraction_bijective
#check S1828Quot_mk_apply
#check S1828SliceFillsOver
#check S1828ModelHomEquivMissing_iff
#check S1828CoverModelHomEquivData_filling
#check S1828ModelHomEquivMissing_of_slice
#check S1828ToCoverMap_id
#check S1828ToCoverMap_comp
#check S1828SliceHomEquiv
#check S1828StrictHomEquiv
#check S1828R1
#check S1828OverToSlice
#check S1828R1ModelCategory
#check S1828SmallRawCoverData
#check S1828SmallRawCoverDataRequired
#check S1828CoverCategory01
#check S1828AffineCoverModelMissing_of_slice

#print axioms S1828SliceCoverEquiv
#print axioms S1828SliceBijective
#print axioms S1828QuotExtraction_bijective
#print axioms S1828ModelHomEquivMissing_iff
#print axioms S1828CoverModelHomEquivData_filling
#print axioms S1828ModelHomEquivMissing_of_slice
#print axioms S1828StrongTransOfHom_id
#print axioms S1828ToCoverMap_id
#print axioms S1828ToCoverMap_comp
#print axioms S1828SliceHomEquiv
#print axioms S1828StrictHomEquiv
#print axioms S1828R1
#print axioms S1828R1ModelCategory
#print axioms S1828SmallRawCoverDataRequired
#print axioms S1828CoverCategory01
#print axioms S1828AffineCoverModelMissing_of_slice

end LeanFormal.IUT.XiFPaper.S1828SliceR1Actual
