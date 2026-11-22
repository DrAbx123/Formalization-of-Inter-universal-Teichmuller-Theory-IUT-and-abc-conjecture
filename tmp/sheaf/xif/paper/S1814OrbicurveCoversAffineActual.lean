/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1757SliceFunctorActual
import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual
import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations

/-!
# S1814: finite-etale covers of the S1726 orbicurve versus covers of Spec R'

## The question

S1799 constructs, for every commutative ring R, the actual equivalence

  (CommAlgCat.FiniteEtale R)^op ≌ FiniteEtaleCover (Spec R)

(S1799AffineFiniteEtaleEquivActual.affineFiniteEtaleEquivalence).  In S1726 the
D6 orbicurve S1726Orbicurve is the represented etale stack of the affine model

  S1726AffineOver = Spec R',   R' = S1726CoordinateRing.

The target asked by S1814 is a category equivalence

  OrbicurveFiniteEtaleCover S1726Orbicurve ≌ FiniteEtaleCover (Spec R')

(or an equivalent cover category), obtained from the represented stack, finite
etale base change, and the 2-Yoneda comparison, or else a precise statement of
the first missing theorem.

## What is constructed unconditionally

* S1814SliceToCover : S1733Slice ⥤ FiniteEtaleCover (Spec R') sends an affine
  finite etale scheme Spec A ⟶ Spec R' to the corresponding finite etale
  cover of Spec R'.  It is proved full, faithful and essentially surjective;
  essential surjectivity uses S1799's theorem that every finite etale cover of
  an affine base has affine carrier and is Spec of its global sections.

* S1814SliceEquiv : S1733Slice ≌ FiniteEtaleCover (Spec R'), the resulting
  genuine equivalence of categories.

* S1814AlgEquiv : (CommAlgCat.FiniteEtale R')^op ≌ FiniteEtaleCover (Spec R'),
  the S1799 equivalence at the actual ring R'.

* S1814SliceAlgEquiv : S1733Slice ≌ (CommAlgCat.FiniteEtale R')^op, obtained by
  composing the two equivalences above.

Thus the affine finite-etale slice over Spec R' and the category of finite
etale covers of Spec R' are actually equivalent; no equivalence is assumed.

## The exact reduction of the orbicurve target

Let S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve, with S1728's
2-isomorphism quotient category structure.  We prove

  S1814OrbicurveAffineEquivalence
    = Nonempty (S1728Cover ≌ FiniteEtaleCover (Spec R'))
  ↔ S1733CoverSliceEquivalence
    = Nonempty (S1728Cover ≌ S1733Slice)
  ↔ S1743SliceFunctorMissing
  ↔ S1814FirstMissing,
    = ∃ F : S1728Cover ⥤ S1733Slice, Nonempty F.FullyFaithful ∧ F.EssSurj.

So the target is exactly the existing S1733/S1743 affine-slice comparison,
composed with the actual slice equivalence constructed here.  No new gap is
introduced and the target is not weakened.

## The precise first missing data on the canonical route

The canonical comparison functor is S1757's S1757Functor h, whose object map is
the affine base-change model S1743Object.  We prove that the following three
genuinely missing statements are sufficient:

* stack representation (S1814StackRepresentation = S1756FirstMissing): the
  identity-point self-endomorphism of every affine model is the identity; this
  is what supplies the lift section h : S1757LiftSection;
* cover-map comparison (full faithfulness of S1757Functor h); this is the
  missing comparison between actual 2-isomorphism classes of cover maps and
  scheme morphisms of their affine models;
* essential surjectivity (S1814EssSurjMissing = S1757EssSurjMissing): every
  affine finite etale scheme over Spec R' is the model of an actual cover.

The conditional construction is S1814_target_of_canonicalData.  The named
statement S1814CoverMapComparison = S1755ModelHomEquivMissing records the raw
hom comparison and is proved to give bijectivity of S1755's extraction and
S1733's affine cover-model theorem (S1814_coverMapComparison_bijective,
S1814_affineCoverModel_of_comparison).  Full faithfulness on 2-isomorphism
classes is a further compatibility statement, not a consequence of the raw
bijection alone (see S1787 for the precise functoriality analysis).

## Honest boundary

No equivalence OrbicurveFiniteEtaleCover S1726Orbicurve ≌ FiniteEtaleCover
(Spec R') is asserted: it is proved equivalent to the existing missing affine
slice comparison, and hence remains open.  In particular the stack
representation S1756FirstMissing, the cover-map comparison and the extension
statement are not inhabited here.  No sorry, no new axiom, no Shrink, ULift,
PUnit, and no fake category or equivalence is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual

open CategoryTheory
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1757SliceFunctorActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual

/-! ## 1. The affine finite-etale slice and finite etale covers of Spec R' -/

/-- The base scheme Spec R'. -/
abbrev S1814Base : Scheme := S1726AffineScheme

/-- The target category of finite etale covers of Spec R'. -/
abbrev S1814Target : Type 1 := FiniteEtaleCover S1814Base

/-- The forgetful functor from the affine finite-etale slice over Spec R' to
finite etale covers of Spec R': an object is literally a finite etale morphism
Spec A ⟶ Spec R', and a morphism is a commuting triangle. -/
noncomputable def S1814SliceToCover : S1733Slice ⥤ S1814Target where
  obj X := FiniteEtaleCover.mk X.hom X.prop.2 X.prop.1
  map {X Y} f :=
    ObjectProperty.homMk
      (Over.homMk (Scheme.Spec.map (CostructuredArrow.Hom.left f.hom))
        (CostructuredArrow.Hom.w f.hom))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change Scheme.Spec.map
      (CostructuredArrow.Hom.left (MorphismProperty.Comma.Hom.hom (𝟙 X))) = 𝟙 _
    simp [CostructuredArrow.Hom.left]
    rfl
  map_comp {X Y Z} f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change Scheme.Spec.map
      (CostructuredArrow.Hom.left (MorphismProperty.Comma.Hom.hom (f ≫ g))) =
      Scheme.Spec.map
        (CostructuredArrow.Hom.left (MorphismProperty.Comma.Hom.hom f)) ≫
      Scheme.Spec.map
        (CostructuredArrow.Hom.left (MorphismProperty.Comma.Hom.hom g))
    rw [← Scheme.Spec.map_comp]
    rfl

/-- The functor to finite etale covers is faithful. -/
instance S1814SliceToCover_faithful : S1814SliceToCover.Faithful where
  map_injective {X Y} f g h := by
    have hleft : Scheme.Spec.map (CostructuredArrow.Hom.left f.hom) =
        Scheme.Spec.map (CostructuredArrow.Hom.left g.hom) :=
      congrArg (fun m : S1814SliceToCover.obj X ⟶ S1814SliceToCover.obj Y =>
        Over.Hom.left m.hom) h
    have hleft' : CostructuredArrow.Hom.left f.hom =
        CostructuredArrow.Hom.left g.hom :=
      Scheme.Spec.map_injective hleft
    apply MorphismProperty.Comma.Hom.ext
    · exact hleft'
    · exact Subsingleton.elim _ _

/-- The functor to finite etale covers is full. -/
instance S1814SliceToCover_full : S1814SliceToCover.Full where
  map_surjective {X Y} h := by
    let f : X.left ⟶ Y.left := Scheme.Spec.preimage (Over.Hom.left h.hom)
    have hfmap : Scheme.Spec.map f = Over.Hom.left h.hom :=
      Scheme.Spec.map_preimage _
    refine ⟨MorphismProperty.CostructuredArrow.homMk f trivial ?_, ?_⟩
    · rw [hfmap]
      exact h.hom.w
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change Scheme.Spec.map f = Over.Hom.left h.hom
      exact hfmap

/-- The affine slice object attached to a finite etale cover C of Spec R': the
spectrum of the ring of global sections of C, with the structure morphism of
S1799's sections cover. -/
noncomputable def S1814CoverToSlice (C : S1814Target) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤)
    (A := Opposite.op (CommRingCat.of
      (coverSectionsFiniteEtale S1726CoordinateRing C).obj))
    (finiteEtaleStructureMap S1726CoordinateRing
      (coverSectionsFiniteEtale S1726CoordinateRing C))
    ⟨finiteEtaleStructureMap_finite S1726CoordinateRing
        (coverSectionsFiniteEtale S1726CoordinateRing C),
      finiteEtaleStructureMap_etale S1726CoordinateRing
        (coverSectionsFiniteEtale S1726CoordinateRing C)⟩

/-- The functor sends the sections object of C definitionally to S1799's
sections cover of C. -/
theorem S1814SliceToCover_coverToSlice_obj (C : S1814Target) :
    S1814SliceToCover.obj (S1814CoverToSlice C) =
      coverSectionsCover S1726CoordinateRing C := rfl

/-- Every finite etale cover of Spec R' is isomorphic to the image of its affine
sections object. -/
theorem S1814SliceToCover_coverToSlice_iso (C : S1814Target) :
    Nonempty (S1814SliceToCover.obj (S1814CoverToSlice C) ≅ C) :=
  ⟨(coverSections_iso S1726CoordinateRing C).some.symm⟩

/-- The functor to finite etale covers is essentially surjective. -/
instance S1814SliceToCover_essSurj : S1814SliceToCover.EssSurj :=
  ⟨fun C => ⟨S1814CoverToSlice C,
    ⟨(coverSections_iso S1726CoordinateRing C).some.symm⟩⟩⟩

instance S1814SliceToCover_isEquivalence : S1814SliceToCover.IsEquivalence where
  faithful := S1814SliceToCover_faithful
  full := S1814SliceToCover_full
  essSurj := S1814SliceToCover_essSurj

/-- The affine finite-etale slice over Spec R' is equivalent to the category of
finite etale covers of Spec R'. -/
noncomputable def S1814SliceEquiv : S1733Slice ≌ S1814Target :=
  S1814SliceToCover.asEquivalence

@[simp] theorem S1814SliceEquiv_functor :
    S1814SliceEquiv.functor = S1814SliceToCover := rfl

/-! ## 2. Compatibility with S1799 -/

/-- The S1799 equivalence at the actual ring R'. -/
noncomputable def S1814AlgEquiv :
    (CommAlgCat.FiniteEtale.{0} S1726CoordinateRing)ᵒᵖ ≌ S1814Target :=
  affineFiniteEtaleEquivalence S1726CoordinateRing

/-- The affine finite-etale slice is equivalent to finite etale R'-algebras. -/
noncomputable def S1814SliceAlgEquiv :
    S1733Slice ≌ (CommAlgCat.FiniteEtale.{0} S1726CoordinateRing)ᵒᵖ :=
  S1814SliceEquiv.trans S1814AlgEquiv.symm

/-! ## 3. The orbicurve cover category and the target equivalence -/

/-- The category structure on the actual orbicurve cover type: the
2-isomorphism quotient category of S1728. -/
local instance S1814CoverCategory : Category.{1, 1} S1728Cover := S1728ActualCategory11

/-- The target equivalence between the actual finite etale covers of the S1726
orbicurve and finite etale covers of Spec R'. -/
def S1814OrbicurveAffineEquivalence : Prop :=
  Nonempty (S1728Cover ≌ S1814Target)

/-- The exact target equivalence, in terms of S1799's finite-etale-algebra
category. -/
theorem S1814_target_iff_algebraEquiv :
    S1814OrbicurveAffineEquivalence ↔
      Nonempty (S1728Cover ≌
        (CommAlgCat.FiniteEtale.{0} S1726CoordinateRing)ᵒᵖ) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans S1814AlgEquiv.symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans S1814AlgEquiv⟩

/-- Exact reduction of the target to the affine finite-etale slice. -/
theorem S1814_target_iff_slice :
    S1814OrbicurveAffineEquivalence ↔ S1733CoverSliceEquivalence := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans S1814SliceEquiv.symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans S1814SliceEquiv⟩

/-- The target equivalence is exactly S1743's missing slice functor. -/
theorem S1814_target_iff_sliceFunctorMissing :
    S1814OrbicurveAffineEquivalence ↔ S1743SliceFunctorMissing :=
  S1814_target_iff_slice.trans S1743SliceFunctorMissing_iff.symm

/-- The target equivalence is exactly the existence of a fully faithful,
essentially surjective functor from the actual cover category to the affine
finite-etale slice. -/
theorem S1814_target_iff_exists_sliceFunctor :
    S1814OrbicurveAffineEquivalence ↔
      ∃ F : S1728Cover ⥤ S1733Slice, Nonempty F.FullyFaithful ∧ F.EssSurj :=
  S1814_target_iff_slice.trans S1755SliceFunctorMissing_iff.symm

/-- The target equivalence from an affine-slice equivalence. -/
theorem S1814_target_of_sliceEquivalence (h : S1733CoverSliceEquivalence) :
    S1814OrbicurveAffineEquivalence :=
  S1814_target_iff_slice.mpr h

/-- Conversely, the target equivalence gives the affine-slice equivalence. -/
theorem S1814_sliceEquivalence_of_target (h : S1814OrbicurveAffineEquivalence) :
    S1733CoverSliceEquivalence :=
  S1814_target_iff_slice.mp h

/-! ## 4. The precise missing statements -/

/-- The exact first missing theorem for the target, in functor form. -/
def S1814FirstMissing : Prop :=
  ∃ F : S1728Cover ⥤ S1733Slice, Nonempty F.FullyFaithful ∧ F.EssSurj

/-- The target equivalence is exactly S1814FirstMissing. -/
theorem S1814_target_iff_firstMissing :
    S1814OrbicurveAffineEquivalence ↔ S1814FirstMissing :=
  S1814_target_iff_slice.trans S1755SliceFunctorMissing_iff.symm

/-- The first missing theorem is exactly S1743's missing slice functor. -/
theorem S1814_firstMissing_iff_sliceFunctorMissing :
    S1814FirstMissing ↔ S1743SliceFunctorMissing :=
  S1755SliceFunctorMissing_iff.trans S1743SliceFunctorMissing_iff.symm

/-- Stack representation, named. -/
def S1814StackRepresentation : Prop := S1756FirstMissing

/-- The raw cover-map comparison, named. -/
def S1814CoverMapComparison : Prop := S1755ModelHomEquivMissing

/-- The extension/essential-surjectivity statement, named. -/
def S1814EssSurjMissing : Prop := S1757EssSurjMissing

/-- The S1756 first missing statement supplies the canonical lift section. -/
theorem S1814_liftSection_of_firstMissing (h : S1756FirstMissing) :
    S1757LiftSection :=
  fun A => (S1756Unit_iff_end A).mpr (h A)

/-- The canonical comparison data: stack representation (as the lift section),
full faithfulness of the canonical functor, and essential surjectivity. -/
structure S1814CanonicalComparisonData where
  /-- The lift section, equivalent to S1756's stack representation. -/
  liftSection : S1757LiftSection
  /-- Full faithfulness of the canonical S1757 functor. -/
  fullyFaithful : (S1757Functor liftSection).FullyFaithful
  /-- Essential surjectivity of the canonical S1757 functor. -/
  essSurj : S1757EssSurjMissing

/-- The canonical data gives the exact first missing theorem. -/
theorem S1814_firstMissing_of_canonicalData (d : S1814CanonicalComparisonData) :
    S1814FirstMissing :=
  ⟨S1757Functor d.liftSection,
    ⟨⟨d.fullyFaithful⟩, S1757EssSurj_of d.liftSection d.essSurj⟩⟩

/-- Stack representation plus full faithfulness and essential surjectivity of
the canonical functor give the first missing theorem. -/
theorem S1814_firstMissing_of_stackRepresentation
    (hrep : S1756FirstMissing)
    (hff : (S1757Functor (S1814_liftSection_of_firstMissing hrep)).FullyFaithful)
    (hess : S1757EssSurjMissing) :
    S1814FirstMissing :=
  ⟨S1757Functor (S1814_liftSection_of_firstMissing hrep),
    ⟨⟨hff⟩, S1757EssSurj_of _ hess⟩⟩

/-- The target equivalence from a lift section, full faithfulness and essential
surjectivity of the canonical S1757 functor. -/
theorem S1814_target_of_liftSection
    (h : S1757LiftSection)
    (hff : (S1757Functor h).FullyFaithful)
    (hess : S1757EssSurjMissing) :
    S1814OrbicurveAffineEquivalence :=
  S1814_target_iff_slice.mpr (S1757CoverSliceEquivalence_of h hff hess)

/-- The target equivalence from S1743's comparison with the fixed affine-model
object map. -/
theorem S1814_target_of_sliceComparison (d : S1743CoverSliceComparison) :
    S1814OrbicurveAffineEquivalence :=
  S1814_target_of_sliceEquivalence
    (S1743CoverSliceEquivalence_of_comparison d)

/-- The canonical conditional construction of the target equivalence from
stack representation, the cover-map comparison, and essential surjectivity. -/
theorem S1814_target_of_canonicalData
    (hrep : S1756FirstMissing)
    (hff : (S1757Functor (S1814_liftSection_of_firstMissing hrep)).FullyFaithful)
    (hess : S1757EssSurjMissing) :
    S1814OrbicurveAffineEquivalence :=
  S1814_target_iff_slice.mpr
    (S1757CoverSliceEquivalence_of _ hff hess)

/-- Stack representation is exactly S1743's source-retraction statement. -/
theorem S1814_stackRepresentation_iff_sourceRetraction :
    S1814StackRepresentation ↔ S1743SourceRetraction :=
  S1756Retraction_iff_firstMissing.symm

/-- The cover-map comparison gives bijectivity of S1755's extraction. -/
theorem S1814_coverMapComparison_bijective (h : S1814CoverMapComparison) :
    ∀ A B : S1728Cover, Function.Bijective (S1755ModelHomOfCoverMap A B) :=
  S1755ModelHomEquivMissing_iff_bijective.mp h

/-- The cover-map comparison also yields S1733's affine cover-model theorem. -/
theorem S1814_affineCoverModel_of_comparison (h : S1814CoverMapComparison) :
    S1733AffineCoverModelMissing :=
  S1755AffineCoverModelMissing_of_modelHomEquiv h

/-! ## 5. Target-locked type checks -/

#check S1814SliceToCover
#check S1814SliceEquiv
#check S1814SliceToCover_coverToSlice_iso
#check S1814AlgEquiv
#check S1814SliceAlgEquiv
#check S1814OrbicurveAffineEquivalence
#check S1814_target_iff_algebraEquiv
#check S1814_target_iff_slice
#check S1814_target_iff_sliceFunctorMissing
#check S1814_target_iff_exists_sliceFunctor
#check S1814_target_of_sliceEquivalence
#check S1814_sliceEquivalence_of_target
#check S1814FirstMissing
#check S1814_target_iff_firstMissing
#check S1814_firstMissing_iff_sliceFunctorMissing
#check S1814StackRepresentation
#check S1814CoverMapComparison
#check S1814EssSurjMissing
#check S1814_liftSection_of_firstMissing
#check S1814CanonicalComparisonData
#check S1814_firstMissing_of_canonicalData
#check S1814_firstMissing_of_stackRepresentation
#check S1814_target_of_canonicalData
#check S1814_target_of_liftSection
#check S1814_target_of_sliceComparison
#check S1814_stackRepresentation_iff_sourceRetraction
#check S1814_coverMapComparison_bijective
#check S1814_affineCoverModel_of_comparison

/-! ## 6. Axiom footprint -/

#print axioms S1814SliceToCover
#print axioms S1814SliceEquiv
#print axioms S1814AlgEquiv
#print axioms S1814SliceAlgEquiv
#print axioms S1814_target_iff_slice
#print axioms S1814_target_iff_sliceFunctorMissing
#print axioms S1814_target_iff_exists_sliceFunctor
#print axioms S1814_target_iff_firstMissing
#print axioms S1814_target_of_canonicalData
#print axioms S1814_target_of_liftSection
#print axioms S1814_target_of_sliceComparison
#print axioms S1814_stackRepresentation_iff_sourceRetraction
#print axioms S1814_coverMapComparison_bijective
#print axioms S1814_affineCoverModel_of_comparison

end LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual

end