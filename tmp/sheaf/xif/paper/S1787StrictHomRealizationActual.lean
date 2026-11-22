/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1754OrbicurvePiFieldsActual
import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual
import tmp.sheaf.xif.paper.S1784SourceRetractionUnitActual

/-!
# S1787: the strict hom realization of the actual cover maps

## Question

S1754 isolated the five categorical fields of the D6 datum as

  S1754S1726StrictRealizationMissing coverCategory
    = Nonempty (S1754StrictHomEquiv (F := S1726K) (X := S1726Orbicurve)),

i.e. hom-wise equivalences

  (A ⟶ B) ≃ OrbicurveFiniteEtaleCoverMap A B

which are compatible with identities and composition up to 2-isomorphism.
Here (A ⟶ B) is the hom type of the chosen small cover category.

The task of this file is to construct this residual from the S1742 2-Yoneda
comparison, the S1755 extraction of a model morphism from a cover map, and the
S1756/S1784 two-pullback analysis of the identity-point base change, or else
to state the exact remaining missing input.

## What is available

* S1742/S1743: for two *representable* etale stacks, evaluation at the
  identity section is a bijection on 2-isomorphism classes between strong
  transformations and scheme morphisms.  It is compatible with vertical
  composition on the nose (S1743YonedaEval_vcomp).

* S1755: for covers A B, every actual cover map f : A ⟶ B induces a cone over
  the identity-point square of B with apex the affine model of A.  Its lift
  S1755Lift A B f is a strong transformation from the model of A to the model
  of B, and evaluation produces

    S1755ModelHomOfCoverMap A B f : S1733Model A ⟶ S1733Model B.

  The map is faithful on 2-isomorphism classes (S1755CoverMapRel_of_modelHom_eq),
  but its inverse is NOT constructed: that is S1755ModelHomEquivMissing.

* S1756/S1784: the identity-point square has an unconditional counit
  lift ≫ toSource ≅ 𝟙 and a missing unit toSource ≫ lift ≅ 𝟙.  S1784 shows
  that the recorded TwoPullbackWitness fields do not even force the unit, and
  isolates the missing half of the bicategorical universal property as
  S1784LiftEssSurj.

## Results of this file

1. S1787LiftFunctorial: the precise 2-categorical input on the S1755 lift that
   the equivalence in R1 needs.  It has exactly two components:

     lift A A (id A) ≅ 𝟙 (model A),

     lift A B f ≫ lift B C g ≅ lift A C (comp f g).

   This is strictly more than "the source is a retract of the model": it is
   functoriality of the extraction of model morphisms.

2. S1787LiftFunctorial_of_liftEssSurj: S1784LiftEssSurj for every cover
   implies S1787LiftFunctorial.  The proof only uses the two projection
   2-isomorphisms of the S1755 lift and the missing essential-surjectivity
   half of the two-pullback universal property.

3. S1787ExtractionId_of_liftFunctorial,
   S1787ExtractionComp_of_liftFunctorial: the lift functoriality makes the
   S1742 evaluation of the S1755 extraction strictly compatible with
   identities and composition.

4. S1787R1ModelCategory_of_liftFunctorial_modelHomEquiv: R1 for the canonical
   model category S1733ModelCategory follows from

     (i) the S1755 hom-wise bijectivity S1755ModelHomEquivMissing, and
     (ii) the lift functoriality S1787LiftFunctorial.

   The conjunction is packaged as S1787FirstMissing, with main theorem
   S1787R1ModelCategory_of_firstMissing.  In particular, R1 follows from
   S1755ModelHomEquivMissing together with S1784LiftEssSurj for all covers.

5. S1787AffineCoverModelMissing_of_R1Model: R1 for the model category gives
   S1733's affine cover model (with the fixed S1733Model), hence the S1728
   small raw cover data.  Thus R1 is at least as strong as the hom-wise
   smallness comparison; the additional content of R1 is exactly the
   id/comp compatibility.

## The exact missing input, and why S1756FirstMissing is not it

S1756FirstMissing is the equation S1756End A = 𝟙.  Equivalently, by
S1756Unit_iff_end, it is the existence of the unit 2-cell
toSource ≫ lift ≅ 𝟙, i.e. the statement that the cover source is a retract of
its affine model.  That is a statement about *one* composite of the two
1-cells of the base-change square.

R1 needs two further things:

* a hom-wise bijection between the model homs and the actual cover maps
  (S1755ModelHomEquivMissing), and
* functoriality of that bijection: the S1755 extraction must send identities
  and composites to identities and composites, up to 2-isomorphism
  (S1787LiftFunctorial).

Neither follows from the source retraction alone.  S1784's analysis shows that
S1756FirstMissing does not even give the lift functoriality: the recorded
TwoPullbackWitness has no property forcing the lift of the pullback's own cone
to be the identity.  In this file S1787LiftFunctorial is therefore an honest
hypothesis, not a consequence of S1756FirstMissing, and it is not inhabited.
The hom-wise bijection S1755ModelHomEquivMissing is likewise not inhabited.
It is a bijection on actual cover maps, not merely on 2-isomorphism classes:
S1755 proves only that equal extracted model morphisms force the cover maps to
be 2-isomorphic (faithfulness on 2-isomorphism classes).  It does not prove
injectivity on representatives of a 2-isomorphism class, so this component is
a strictness/smallness input, potentially stronger than representability of
the cover source by its model.  It is recorded, not asserted.

No sorry, no axiom, no Shrink, no ULift, no PUnit, and no fake category,
equivalence or cover map is introduced.  The conditional theorems are real
proofs from the stated inputs; the residuals are recorded as types.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1787StrictHomRealizationActual

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
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual

/-! ## 1. The exact 2-categorical input -/

/-- The S1784 missing half of the two-pullback universal property, for every
cover.  This is the statement that a 1-cell into the affine model whose two
projections agree with a cone is 2-isomorphic to the universal lift. -/
def S1787LiftEssSurjAll : Prop :=
  ∀ A : S1728Cover, S1784LiftEssSurj A

/-- The precise functoriality of the S1755 lift which is needed for R1.  It is
weaker than full essential surjectivity of the two-pullback comparison; it
only asks for the two coherence 2-isomorphisms of the canonical lift. -/
def S1787LiftFunctorial : Prop :=
  (∀ A : S1728Cover,
    Nonempty (Iso
      (S1755Lift A A (S1641CoverMapId A))
      (Pseudofunctor.StrongTrans.id (S1755ModelStack A)))) ∧
  (∀ {A B C : S1728Cover} (f : S1728CoverMap A B) (g : S1728CoverMap B C),
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1755Lift A B f) (S1755Lift B C g))
      (S1755Lift A C (S1641CoverMapComp f g))))

/-- The identity component of the lift functoriality, extracted from the
S1784 essential-surjectivity half. -/
theorem S1787Lift_id_iso_of_liftEssSurj
    (hL : S1787LiftEssSurjAll) (A : S1728Cover) :
    Nonempty (Iso
      (S1755Lift A A (S1641CoverMapId A))
      (Pseudofunctor.StrongTrans.id (S1755ModelStack A))) := by
  let W : EtaleStackPseudofunctor S1726K := S1743ModelStack A
  let c : (S1743Square A).Cone W := S1755Cone A A (S1641CoverMapId A)
  have hX : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id W)
        (S1743Square A).toX) c.toX) := by
    refine ⟨?_⟩
    exact (S1756LeftUnitorIso (S1756ToSource A)).trans
      (S1756RightUnitorIso (S1756ToSource A)).symm
  have hY : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id W)
        (S1743Square A).toY) c.toY) := by
    refine ⟨?_⟩
    exact S1756LeftUnitorIso (S1756ProjectionMap A)
  have h := hL A W c (Pseudofunctor.StrongTrans.id W) hX hY
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/-- The composition component of the lift functoriality, extracted from the
S1784 essential-surjectivity half. -/
theorem S1787Lift_comp_iso_of_liftEssSurj
    (hL : S1787LiftEssSurjAll) {A B C : S1728Cover}
    (f : S1728CoverMap A B) (g : S1728CoverMap B C) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1755Lift A B f) (S1755Lift B C g))
      (S1755Lift A C (S1641CoverMapComp f g))) := by
  let Lf : Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743ModelStack B) :=
    S1755Lift A B f
  let Lg : Pseudofunctor.StrongTrans (S1743ModelStack B) (S1743ModelStack C) :=
    S1755Lift B C g
  let c : (S1743Square C).Cone (S1743ModelStack A) :=
    S1755Cone A C (S1641CoverMapComp f g)
  have hX : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lf Lg) (S1743Square C).toX) c.toX) := by
    refine ⟨?_⟩
    change Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lf Lg) (S1756ToSource C))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp f.map g.map))
    have h1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp Lf Lg) (S1756ToSource C))
        (Pseudofunctor.StrongTrans.vcomp Lf
          (Pseudofunctor.StrongTrans.vcomp Lg (S1756ToSource C))) :=
      S1756AssociatorIso Lf Lg (S1756ToSource C)
    have h2 : Iso
        (Pseudofunctor.StrongTrans.vcomp Lf
          (Pseudofunctor.StrongTrans.vcomp Lg (S1756ToSource C)))
        (Pseudofunctor.StrongTrans.vcomp Lf
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource B) g.map)) :=
      S1756WhiskerLeftIso Lf _ _ (S1755Lift_toX B C g)
    have h3 : Iso
        (Pseudofunctor.StrongTrans.vcomp Lf
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource B) g.map))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp Lf (S1756ToSource B)) g.map) :=
      (S1756AssociatorIso Lf (S1756ToSource B) g.map).symm
    have h4 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp Lf (S1756ToSource B)) g.map)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) g.map) :=
      S1756WhiskerRightIso _ _ g.map (S1755Lift_toX A B f)
    have h5 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) g.map)
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp f.map g.map)) :=
      S1756AssociatorIso (S1756ToSource A) f.map g.map
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hY : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lf Lg) (S1743Square C).toY) c.toY) := by
    refine ⟨?_⟩
    have h1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp Lf Lg) (S1756ProjectionMap C))
        (Pseudofunctor.StrongTrans.vcomp Lf
          (Pseudofunctor.StrongTrans.vcomp Lg (S1756ProjectionMap C))) :=
      S1756AssociatorIso Lf Lg (S1756ProjectionMap C)
    have h2 : Iso
        (Pseudofunctor.StrongTrans.vcomp Lf
          (Pseudofunctor.StrongTrans.vcomp Lg (S1756ProjectionMap C)))
        (Pseudofunctor.StrongTrans.vcomp Lf (S1756ProjectionMap B)) :=
      S1756WhiskerLeftIso Lf _ _ (S1755Lift_toY B C g)
    have h3 : Iso
        (Pseudofunctor.StrongTrans.vcomp Lf (S1756ProjectionMap B))
        (S1756ProjectionMap A) :=
      S1755Lift_toY A B f
    exact h1.trans (h2.trans h3)
  have h := hL C (S1743ModelStack A) c
    (Pseudofunctor.StrongTrans.vcomp Lf Lg) hX hY
  rcases h with ⟨e⟩
  exact ⟨e⟩

/-- S1784's missing half of the two-pullback universal property implies the
functoriality of the S1755 lift. -/
theorem S1787LiftFunctorial_of_liftEssSurj
    (hL : S1787LiftEssSurjAll) : S1787LiftFunctorial :=
  ⟨fun A => S1787Lift_id_iso_of_liftEssSurj hL A,
    fun f g => S1787Lift_comp_iso_of_liftEssSurj hL f g⟩

/-! ## 2. The extraction is compatible with identities and composition -/

/-- The evaluation of the S1755 extraction.  This is just S1742's evaluation
of the lifted strong transformation. -/
theorem S1787ExtractionId_of_liftFunctorial
    (h : S1787LiftFunctorial) :
    ∀ A : S1728Cover,
      S1755ModelHomOfCoverMap A A (S1641CoverMapId A) = 𝟙 (S1733Model A) := by
  intro A
  have h1 := S1743YonedaEval_congr_iso (S1733Model A) (S1733Model A) (h.1 A).some
  change S1743YonedaEval (S1733Model A) (S1733Model A)
      (S1755Lift A A (S1641CoverMapId A)) =
    S1743YonedaEval (S1733Model A) (S1733Model A)
      (Pseudofunctor.StrongTrans.id (S1743Y (S1733Model A))) at h1
  rw [S1756YonedaEval_id] at h1
  change S1743YonedaEval (S1733Model A) (S1733Model A)
      (S1755Lift A A (S1641CoverMapId A)) = 𝟙 (S1733Model A)
  exact h1

/-- The S1742 evaluation of the S1755 extraction is strictly compatible with
composition. -/
theorem S1787ExtractionComp_of_liftFunctorial
    (h : S1787LiftFunctorial) :
    ∀ {A B C : S1728Cover} (f : S1728CoverMap A B) (g : S1728CoverMap B C),
      S1755ModelHomOfCoverMap A C (S1641CoverMapComp f g) =
        S1755ModelHomOfCoverMap A B f ≫ S1755ModelHomOfCoverMap B C g := by
  intro A B C f g
  have h1 := S1743YonedaEval_congr_iso (S1733Model A) (S1733Model C)
    (h.2 f g).some
  have h2 := S1743YonedaEval_vcomp (S1733Model A) (S1733Model B) (S1733Model C)
    (S1755Lift A B f) (S1755Lift B C g)
  have h3 : S1743YonedaEval (S1733Model A) (S1733Model C)
        (S1755Lift A C (S1641CoverMapComp f g)) =
      S1743YonedaEval (S1733Model A) (S1733Model B) (S1755Lift A B f) ≫
        S1743YonedaEval (S1733Model B) (S1733Model C) (S1755Lift B C g) :=
    h1.symm.trans h2
  change S1743YonedaEval (S1733Model A) (S1733Model C)
      (S1755Lift A C (S1641CoverMapComp f g)) =
    S1743YonedaEval (S1733Model A) (S1733Model B) (S1755Lift A B f) ≫
      S1743YonedaEval (S1733Model B) (S1733Model C) (S1755Lift B C g)
  exact h3

/-! ## 3. R1 for the canonical model category -/

/-- **R1 for the canonical affine-model category.**  Assume the hom-wise
bijectivity of the S1755 extraction (S1755ModelHomEquivMissing) and its
functoriality (S1787LiftFunctorial).  Then the actual cover maps are
equivalent to the model homs, compatibly with identities and composition up to
2-isomorphism. -/
theorem S1787R1ModelCategory_of_liftFunctorial_modelHomEquiv
    (hfun : S1787LiftFunctorial)
    (h : S1755ModelHomEquivMissing) :
    S1754S1726StrictRealizationMissing S1733ModelCategory := by
  letI := S1733ModelCategory
  have hbij : ∀ A B : S1728Cover,
      Function.Bijective (S1755ModelHomOfCoverMap A B) :=
    S1755ModelHomEquivMissing_iff_bijective.mp h
  let e : ∀ A B : S1728Cover,
      (S1733Model A ⟶ S1733Model B) ≃ S1728CoverMap A B :=
    fun A B => (Equiv.ofBijective (S1755ModelHomOfCoverMap A B) (hbij A B)).symm
  refine ⟨?_⟩
  exact
    { equiv := fun A B => e A B
      id_compat := by
        intro A
        have h1 : S1755ModelHomOfCoverMap A A (e A A (𝟙 (S1733Model A))) =
            𝟙 (S1733Model A) :=
          (Equiv.ofBijective (S1755ModelHomOfCoverMap A A) (hbij A A)).right_inv
            (𝟙 (S1733Model A))
        have h2 : S1755ModelHomOfCoverMap A A (S1641CoverMapId A) =
            𝟙 (S1733Model A) :=
          S1787ExtractionId_of_liftFunctorial hfun A
        have hEq : S1755ModelHomOfCoverMap A A (e A A (𝟙 (S1733Model A))) =
            S1755ModelHomOfCoverMap A A (S1641CoverMapId A) :=
          h1.trans h2.symm
        have hrel := S1755CoverMapRel_of_modelHom_eq (A := A) (B := A)
          (f := e A A (𝟙 (S1733Model A))) (g := S1641CoverMapId A) hEq
        change Iso ((e A A (𝟙 (S1733Model A))).map)
          (Pseudofunctor.StrongTrans.id A.source.fiber)
        exact hrel.some
      comp_compat := by
        intro A B C f g
        have h1 : S1755ModelHomOfCoverMap A C
            (e A C (f ≫ g)) = f ≫ g :=
          (Equiv.ofBijective (S1755ModelHomOfCoverMap A C) (hbij A C)).right_inv
            (f ≫ g)
        have h2 : S1755ModelHomOfCoverMap A C
            (S1641CoverMapComp (e A B f) (e B C g)) =
            S1755ModelHomOfCoverMap A B (e A B f) ≫
              S1755ModelHomOfCoverMap B C (e B C g) :=
          S1787ExtractionComp_of_liftFunctorial hfun (e A B f) (e B C g)
        have h3 : S1755ModelHomOfCoverMap A B (e A B f) = f :=
          (Equiv.ofBijective (S1755ModelHomOfCoverMap A B) (hbij A B)).right_inv f
        have h4 : S1755ModelHomOfCoverMap B C (e B C g) = g :=
          (Equiv.ofBijective (S1755ModelHomOfCoverMap B C) (hbij B C)).right_inv g
        have hEq : S1755ModelHomOfCoverMap A C (e A C (f ≫ g)) =
            S1755ModelHomOfCoverMap A C
              (S1641CoverMapComp (e A B f) (e B C g)) := by
          rw [h1, h2, h3, h4]
          rfl
        have hrel := S1755CoverMapRel_of_modelHom_eq (A := A) (B := C)
          (f := e A C (f ≫ g))
          (g := S1641CoverMapComp (e A B f) (e B C g)) hEq
        change Iso ((e A C (f ≫ g)).map)
          (Pseudofunctor.StrongTrans.vcomp ((e A B f).map) ((e B C g).map))
        exact hrel.some }

/-- **R1 from the S1784 essential-surjectivity half and the S1755 hom-wise
bijection.**  This is the advertised construction: no other geometric input is
used. -/
theorem S1787R1ModelCategory_of_liftEssSurj_modelHomEquiv
    (hL : S1787LiftEssSurjAll)
    (h : S1755ModelHomEquivMissing) :
    S1754S1726StrictRealizationMissing S1733ModelCategory :=
  S1787R1ModelCategory_of_liftFunctorial_modelHomEquiv
    (S1787LiftFunctorial_of_liftEssSurj hL) h

/-- **The exact missing input used by this construction of R1.**  It is the
conjunction of the S1755 hom-wise bijection and the functoriality of the S1755
lift.  Neither component is a consequence of S1756FirstMissing: the first is a
bijection on actual cover maps (not just on 2-isomorphism classes), hence a
strictness/smallness input, and the second is the missing functoriality of the
extraction (S1784LiftEssSurj supplies it). -/
def S1787FirstMissing : Prop :=
  S1755ModelHomEquivMissing ∧ S1787LiftFunctorial

/-- R1 for the canonical model category from the packaged missing input. -/
theorem S1787R1ModelCategory_of_firstMissing
    (h : S1787FirstMissing) :
    S1754S1726StrictRealizationMissing S1733ModelCategory :=
  S1787R1ModelCategory_of_liftFunctorial_modelHomEquiv h.2 h.1

/-! ## 4. What R1 gives: the affine cover model of S1733 -/

/-- R1 for the canonical model category is at least as strong as S1733's
missing affine cover model with the fixed S1733Model: it supplies exactly the
missing homEquiv field.  The remaining content of R1 is the compatibility
with identities and composition. -/
theorem S1787AffineCoverModelMissing_of_R1Model
    (h : S1754S1726StrictRealizationMissing S1733ModelCategory) :
    S1733AffineCoverModelMissing := by
  letI := S1733ModelCategory
  rcases h with ⟨s⟩
  exact ⟨
    { model := S1733Model
      toBase := S1733ModelOver
      isAffine := S1743Model_isAffine
      isFinite := fun A => (S1733Model_finiteEtale A).1
      isEtale := fun A => (S1733Model_finiteEtale A).2
      homEquiv := fun A B => s.equiv A B }⟩

/-! ## 5. Relation to the source-retraction statement -/

/-- The S1784 essential-surjectivity half implies S1756FirstMissing, the
source-retraction statement.  This records that S1787LiftFunctorial is a
strictly stronger input than the source retraction: it is the missing
functoriality of the extracted model morphisms, not merely the unit triangle. -/
theorem S1787SourceRetraction_of_liftEssSurj
    (hL : S1787LiftEssSurjAll) : S1756FirstMissing :=
  S1784FirstMissing_of_liftEssSurj hL

/-! ## 6. Checks -/

#check S1787LiftEssSurjAll
#check S1787LiftFunctorial
#check S1787Lift_id_iso_of_liftEssSurj
#check S1787Lift_comp_iso_of_liftEssSurj
#check S1787LiftFunctorial_of_liftEssSurj
#check S1787ExtractionId_of_liftFunctorial
#check S1787ExtractionComp_of_liftFunctorial
#check S1787R1ModelCategory_of_liftFunctorial_modelHomEquiv
#check S1787R1ModelCategory_of_liftEssSurj_modelHomEquiv
#check S1787FirstMissing
#check S1787R1ModelCategory_of_firstMissing
#check S1787AffineCoverModelMissing_of_R1Model
#check S1787SourceRetraction_of_liftEssSurj

#print axioms S1787Lift_id_iso_of_liftEssSurj
#print axioms S1787Lift_comp_iso_of_liftEssSurj
#print axioms S1787LiftFunctorial_of_liftEssSurj
#print axioms S1787ExtractionId_of_liftFunctorial
#print axioms S1787ExtractionComp_of_liftFunctorial
#print axioms S1787R1ModelCategory_of_liftFunctorial_modelHomEquiv
#print axioms S1787R1ModelCategory_of_liftEssSurj_modelHomEquiv
#print axioms S1787R1ModelCategory_of_firstMissing
#print axioms S1787AffineCoverModelMissing_of_R1Model
#print axioms S1787SourceRetraction_of_liftEssSurj

end LeanFormal.IUT.XiFPaper.S1787StrictHomRealizationActual
