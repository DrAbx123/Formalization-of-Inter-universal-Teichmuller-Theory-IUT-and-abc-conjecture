import tmp.sheaf.xif.paper.S2001LiftCommutesActual
import tmp.sheaf.xif.paper.S1841SourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual

/-!
# S2007: discreteness of cover fibres and the first missing input for uniq

## Question

S2001 reduced the remaining site-level uniqueness field `uniq` to the
0-truncation of the fibre categories of a finite-etale cover,

  `S2001CoverFiberDiscrete C := forall U X Y, Subsingleton (X --> Y)`.

The question of this file is whether this discreteness can be derived from the
recorded finite-etale data `C.finiteEtale` (representable finite etaleness of
`C.map`, together with the descent/stack condition `C.source.isStack`), or
whether it isolates a genuinely missing geometric input.

## What is proved here, unconditionally

1. The fibre of every representable etale stack `S1743Y S` is discrete in the
   required sense: `S2007RepresentableFiberSubsingleton`.

2. A quasi-equivalence `S1756StackEquiv P Q` transfers subsingleton hom types
   from `P` to `Q` at every site object.  The proof builds the componentwise
   categorical equivalence from the unit and counit 2-isomorphisms
   (`S2007ComponentEquivalence`) and uses faithfulness of the inverse functor.
   This is `S2007Subsingleton_of_stackEquiv`.

3. Hence `S2001CoverFiberDiscrete C` follows from representability of the
   source of `C` by its identity-point affine model,
   `S2007SourceRepresentable C := Nonempty (S1756StackEquiv (S1743ModelStack C)
   (S1743Source C))`.  This is `S2007CoverFiberDiscrete_of_sourceRepresentable`.

4. S1841 identifies the same hypothesis with the full 2-dimensional universal
   property of the actual identity-point base-change square:
   `S1841FirstMissing <-> S1827FirstMissing`, where
   `S1827ConeEssSurj C` is exactly the missing essential-surjectivity half of
   the recorded weak `TwoPullbackWitness`.  A precise missing input on this
   route is therefore

     `S2007FirstMissing := S1841FirstMissing`
       (equivalently `S2007BaseChangeFullAll := S1827FirstMissing`),

   and it suffices for `S2001UniqFirstMissing`
   (`S2007UniqFirstMissing_of_firstMissing`).  This file proves the sufficiency
   direction only.  It does not claim that `S2007FirstMissing` is necessary for
   `S2001CoverFiberDiscrete`; it is the exact missing input for the
   representability/full-2-universal-property route to it.

## Why this is the exact first missing, and not a consequence of the recorded data

The recorded field `C.finiteEtale` stores, at each scheme-valued point of the
orbicurve, an `EtaleStackBaseChangePresentation`.  Its universal property is
only the weak seven-field `TwoPullbackWitness`.  S1841 proves that the weak
witness schema does not imply the full essential-surjectivity half
(`S1841RecordedWitnessInsufficient`), and S1844 constructs an actual enlarged
affine base-change presentation, with all four objects representable etale
stacks and identity right leg, which satisfies every recorded field but whose
cone comparison is not essentially surjective (`S1844EssSurj_fails`).  Hence the
missing half is genuine data, not a coherence condition on already-given
2-cells; a geometric proof must supply it (or an equivalent source
representability statement).  The recorded `C.finiteEtale` field stores only the
weak witness, so a uniform argument from that recorded data cannot produce the
missing half; a genuine geometric input is required.  This is exactly the
strengthening `S2007AllBaseChangesFull`: full 2-universal property at every
scheme-valued point, not merely the recorded weak witness.

## Honest boundary

`S2007FirstMissing` is not inhabited here.  No cover, stack equivalence, axiom
or 2-cell is fabricated.  The only additional input used is the explicitly
named full 2-universal property.  The sufficiency theorem is honest: it reduces
`S2001CoverFiberDiscrete` to a named, tree-established missing statement, and
the insufficiency theorems show that the recorded weak witnesses cannot supply
that statement uniformly.  No `sorry`, no new axiom, no `Shrink`, `ULift` or
`PUnit`.

Once `S2001CoverFiberDiscrete` is available, S2001's
`siteIsoComma_square_automatic` makes the iso-comma square condition
automatic; the rest of `uniq` is modification bookkeeping.  This file does not
formalise that bookkeeping; it supplies the previously missing discreteness
input (conditionally on the exact first missing) and identifies the boundary
precisely.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2007CoverFiberDiscreteActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1843SourceAllPointsActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual

/-! ## 1. Representable fibres are discrete -/

/-- The fibre of a representable etale stack at a site object is the discrete
category of sections of that object over the representing scheme.  Hence every
hom type in it is a subsingleton. -/
theorem S2007RepresentableFiberSubsingleton (S : SchemeOverField S1726K)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (X Y : (S1743Y S).obj U) : Subsingleton (X ⟶ Y) := by
  let X' : Discrete (U.as.unop ⟶ S) := X
  let Y' : Discrete (U.as.unop ⟶ S) := Y
  change Subsingleton (X' ⟶ Y')
  infer_instance

/-! ## 2. Transfer of hom-subsingletonness along a quasi-equivalence of stacks -/

/-- The unit component of a `S1756StackEquiv` is an isomorphism in `Cat` at
every site object.  This is the componentwise form of the unit 2-isomorphism;
the two inverse laws are read off from the modification inverse laws. -/
theorem S2007UnitComponentIsIso {P Q : EtaleStackPseudofunctor S1726K}
    (E : S1756StackEquiv P Q) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    IsIso (E.unit.hom.as.app U) := by
  refine ⟨E.unit.inv.as.app U, ?_, ?_⟩
  · have h := congrArg (fun m : (Pseudofunctor.StrongTrans.vcomp E.hom E.inv) ⟶
        (Pseudofunctor.StrongTrans.vcomp E.hom E.inv) => m.as.app U) E.unit.hom_inv_id
    simpa only [Pseudofunctor.StrongTrans.homCategory, CategoryStruct.comp, CategoryStruct.id,
      Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Pseudofunctor.StrongTrans.Modification.id_app] using h
  · have h := congrArg (fun m : (Pseudofunctor.StrongTrans.id P) ⟶
        (Pseudofunctor.StrongTrans.id P) => m.as.app U) E.unit.inv_hom_id
    simpa only [Pseudofunctor.StrongTrans.homCategory, CategoryStruct.comp, CategoryStruct.id,
      Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Pseudofunctor.StrongTrans.Modification.id_app] using h

/-- The counit component of a `S1756StackEquiv` is an isomorphism in `Cat` at
every site object. -/
theorem S2007CounitComponentIsIso {P Q : EtaleStackPseudofunctor S1726K}
    (E : S1756StackEquiv P Q) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    IsIso (E.counit.hom.as.app U) := by
  refine ⟨E.counit.inv.as.app U, ?_, ?_⟩
  · have h := congrArg (fun m : (Pseudofunctor.StrongTrans.vcomp E.inv E.hom) ⟶
        (Pseudofunctor.StrongTrans.vcomp E.inv E.hom) => m.as.app U) E.counit.hom_inv_id
    simpa only [Pseudofunctor.StrongTrans.homCategory, CategoryStruct.comp, CategoryStruct.id,
      Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Pseudofunctor.StrongTrans.Modification.id_app] using h
  · have h := congrArg (fun m : (Pseudofunctor.StrongTrans.id Q) ⟶
        (Pseudofunctor.StrongTrans.id Q) => m.as.app U) E.counit.inv_hom_id
    simpa only [Pseudofunctor.StrongTrans.homCategory, CategoryStruct.comp, CategoryStruct.id,
      Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Pseudofunctor.StrongTrans.Modification.id_app] using h

/-- The unit component as an isomorphism of functors. -/
noncomputable def S2007UnitIso {P Q : EtaleStackPseudofunctor S1726K}
    (E : S1756StackEquiv P Q) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Iso ((E.hom.app U).toFunctor ⋙ (E.inv.app U).toFunctor) (𝟭 (P.obj U)) := by
  haveI : IsIso (E.unit.hom.as.app U) := S2007UnitComponentIsIso E U
  have hcomp : (Pseudofunctor.StrongTrans.vcomp E.hom E.inv).app U =
      E.hom.app U ≫ E.inv.app U :=
    Pseudofunctor.StrongTrans.comp_app E.hom E.inv U
  have hid : (Pseudofunctor.StrongTrans.id P).app U = 𝟙 (P.obj U) := rfl
  have h1 : Iso (E.hom.app U ≫ E.inv.app U) (𝟙 (P.obj U)) :=
    eqToIso hcomp.symm ≪≫ asIso (E.unit.hom.as.app U) ≪≫ eqToIso hid
  have h2 := Cat.Hom.toNatIso h1
  simpa using h2

/-- The counit component as an isomorphism of functors. -/
noncomputable def S2007CounitIso {P Q : EtaleStackPseudofunctor S1726K}
    (E : S1756StackEquiv P Q) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Iso ((E.inv.app U).toFunctor ⋙ (E.hom.app U).toFunctor) (𝟭 (Q.obj U)) := by
  haveI : IsIso (E.counit.hom.as.app U) := S2007CounitComponentIsIso E U
  have hcomp : (Pseudofunctor.StrongTrans.vcomp E.inv E.hom).app U =
      E.inv.app U ≫ E.hom.app U :=
    Pseudofunctor.StrongTrans.comp_app E.inv E.hom U
  have hid : (Pseudofunctor.StrongTrans.id Q).app U = 𝟙 (Q.obj U) := rfl
  have h1 : Iso (E.inv.app U ≫ E.hom.app U) (𝟙 (Q.obj U)) :=
    eqToIso hcomp.symm ≪≫ asIso (E.counit.hom.as.app U) ≪≫ eqToIso hid
  have h2 := Cat.Hom.toNatIso h1
  simpa using h2

/-- The componentwise categorical equivalence underlying a quasi-equivalence of
etale stacks. -/
noncomputable def S2007ComponentEquivalence {P Q : EtaleStackPseudofunctor S1726K}
    (E : S1756StackEquiv P Q) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    CategoryTheory.Equivalence (P.obj U) (Q.obj U) :=
  CategoryTheory.Equivalence.mk (E.hom.app U).toFunctor (E.inv.app U).toFunctor
    (S2007UnitIso E U).symm (S2007CounitIso E U)

/-- A quasi-equivalence of etale stacks transfers subsingleton hom types from
its source to its target at every site object.  The proof uses that the inverse
functor is faithful: it maps two parallel morphisms to a hom type of the source,
where they are equal by hypothesis, and faithfulness cancels the inverse. -/
theorem S2007Subsingleton_of_stackEquiv {P Q : EtaleStackPseudofunctor S1726K}
    (E : S1756StackEquiv P Q)
    (hP : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
      (X Y : P.obj U), Subsingleton (X ⟶ Y))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (X Y : Q.obj U) : Subsingleton (X ⟶ Y) := by
  let e := S2007ComponentEquivalence E U
  constructor
  intro f g
  have h : e.inverse.map f = e.inverse.map g :=
    Subsingleton.elim (α := e.inverse.obj X ⟶ e.inverse.obj Y) _ _
  exact e.inverse.map_injective h

/-! ## 3. Source representability implies cover-fibre discreteness -/

/-- Representability of the source of a cover by its identity-point affine
model, expressed as a genuine quasi-equivalence of category-valued etale
stacks.  This is S1756's `S1756SourceRepresentable` written through the
S1743 names. -/
def S2007SourceRepresentable (C : S1728Cover) : Prop :=
  Nonempty (S1756StackEquiv (S1743ModelStack C) (S1743Source C))

/-- The definition is literally S1756's source representability. -/
theorem S2007SourceRepresentable_iff (C : S1728Cover) :
    S2007SourceRepresentable C ↔ S1756SourceRepresentable C :=
  Iff.rfl

/-- A quasi-equivalence of the canonical comparison gives source
representability. -/
theorem S2007SourceRepresentable_of_quasiEquiv (C : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource C)) : S2007SourceRepresentable C :=
  ⟨S1841StackEquivOfQuasiEquiv C h⟩

/-- Source representability implies discreteness of every fibre of the cover
source. -/
theorem S2007CoverFiberDiscrete_of_sourceRepresentable (C : S1728Cover)
    (h : S2007SourceRepresentable C) : S2001CoverFiberDiscrete C := by
  obtain ⟨E⟩ := h
  exact S2007Subsingleton_of_stackEquiv E
    (fun U X Y => S2007RepresentableFiberSubsingleton (S1733Model C) U X Y)

/-- The equivalent form starting from the quasi-equivalence of the canonical
comparison `S1756ToSource C`. -/
theorem S2007CoverFiberDiscrete_of_quasiEquiv (C : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource C)) : S2001CoverFiberDiscrete C :=
  S2007CoverFiberDiscrete_of_sourceRepresentable C
    (S2007SourceRepresentable_of_quasiEquiv C h)

/-- The full 2-dimensional universal property of the actual identity-point
base-change square suffices. -/
theorem S2007CoverFiberDiscrete_of_coneEssSurj (C : S1728Cover)
    (h : S1827ConeEssSurj C) : S2001CoverFiberDiscrete C :=
  S2007CoverFiberDiscrete_of_quasiEquiv C
    (S1841QuasiEquiv_toSource_of_coneEssSurj C h)

/-! ## 4. The exact first missing statement and its consequences -/

/-- The missing half of the 2-dimensional universal property of the actual
identity-point base-change square of a cover.  This is exactly the input that
the recorded weak `TwoPullbackWitness` does not supply. -/
abbrev S2007BaseChangeFull (C : S1728Cover) : Prop :=
  S1827ConeEssSurj C

/-- The full 2-dimensional universal property uniformly over all covers. -/
abbrev S2007BaseChangeFullAll : Prop :=
  S1827FirstMissing

/-- The 2-commutative square of an arbitrary recorded finite-etale base-change
presentation.  It is the generic version of S1743's identity-point square. -/
noncomputable abbrev S2007BaseChangeSquare (C : S1728Cover)
    (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor S1726K T)
      S1726Orbicurve.stack.fiber) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K
        (C.finiteEtale.baseChange T p).pullbackScheme)
      C.source.fiber
      (schemeRepresentableEtalePseudofunctor S1726K T)
      S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk
    (C.finiteEtale.baseChange T p).toSource
    (C.finiteEtale.baseChange T p).projectionMap.transformation
    C.map p (C.finiteEtale.baseChange T p).commutes

/-- The full 2-dimensional universal property of the recorded finite-etale
base-change presentation at every scheme-valued point of the orbicurve.  This is
the exact strengthening of the weak `TwoPullbackWitness` fields stored in
`C.finiteEtale`. -/
def S2007AllBaseChangesFull : Prop :=
  ∀ (C : S1728Cover) (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor S1726K T)
      S1726Orbicurve.stack.fiber),
    S1827EssSurjOf (S2007BaseChangeSquare C T p)
      (C.finiteEtale.baseChange T p).isPullback

/-- The all-base-change full property implies the identity-point full property
used for source representability. -/
theorem S2007AllBaseChangesFull_implies_identity (h : S2007AllBaseChangesFull) :
    S2007BaseChangeFullAll := by
  intro C
  exact h C S1726AffineOver S1733BasePoint

/-- The first missing statement for the cover-fibre discreteness route: every
cover source is represented by its identity-point affine finite-etale model,
equivalently every recorded identity-point base-change square has the full
2-dimensional universal property. -/
abbrev S2007FirstMissing : Prop :=
  S1841FirstMissing

/-- The first missing statement is exactly the full 2-universal property of all
recorded identity-point base-change squares. -/
theorem S2007FirstMissing_iff_full :
    S2007FirstMissing ↔ S2007BaseChangeFullAll :=
  S1841FirstMissing_iff_S1827

/-- The first missing statement in source-representability form. -/
theorem S2007FirstMissing_sourceRepresentable (h : S2007FirstMissing) :
    ∀ C : S1728Cover, S2007SourceRepresentable C :=
  fun C => S2007SourceRepresentable_of_quasiEquiv C (h C)

/-- **The cover-fibre discreteness input for S2001, from the exact first missing
full 2-universal property.** -/
theorem S2007UniqFirstMissing_of_firstMissing (h : S2007FirstMissing) :
    S2001UniqFirstMissing :=
  fun C => S2007CoverFiberDiscrete_of_quasiEquiv C (h C)

/-- The same conclusion from the explicitly named full 2-universal property. -/
theorem S2007UniqFirstMissing_of_full (h : S2007BaseChangeFullAll) :
    S2001UniqFirstMissing :=
  S2007UniqFirstMissing_of_firstMissing (S2007FirstMissing_iff_full.mpr h)

/-- The same conclusion from the full 2-universal property of *every* recorded
finite-etale base-change presentation. -/
theorem S2007UniqFirstMissing_of_allBaseChangesFull
    (h : S2007AllBaseChangesFull) : S2001UniqFirstMissing :=
  S2007UniqFirstMissing_of_full (S2007AllBaseChangesFull_implies_identity h)

/-- The same conclusion from the per-cover full property. -/
theorem S2007CoverFiberDiscrete_of_fullBaseChange (C : S1728Cover)
    (h : S2007BaseChangeFull C) : S2001CoverFiberDiscrete C :=
  S2007CoverFiberDiscrete_of_coneEssSurj C h

/-! ## 5. The recorded weak witness is insufficient

The following are re-exported from S1841 and S1844 to record the boundary: the
weak `TwoPullbackWitness` fields alone do not imply the missing half, and the
actual enlarged affine presentation of S1844 satisfies all seven recorded fields
while failing the essential-surjectivity half. -/

/-- The recorded weak `TwoPullbackWitness` schema does not imply the missing
essential-surjectivity half. -/
theorem S2007RecordedWitnessInsufficient :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S1827EssSurjOf sq w) :=
  S1841RecordedWitnessInsufficient

/-- The S1844 enlarged affine base-change presentation satisfies all seven
recorded fields of a two-pullback witness but fails the missing half. -/
theorem S2007EnlargedPresentationFails :
    ¬ S1827EssSurjOf S1844Square S1844Witness :=
  S1844EssSurj_fails

/-- Consequently no uniform schema over representable squares produces right
cancellation (the uniq-shaped consequence) from the recorded weak witness. -/
theorem S2007RepresentableSchemaFails :
    ¬ (∀ (Q X Y Z : SchemeOverField S1726K)
        (sq : EtalePseudofunctorSquare (S1743Y Q) (S1743Y X) (S1743Y Y) (S1743Y Z))
        (w : sq.TwoPullbackWitness), S1843RightCancelOf sq w) :=
  S1844RepresentableSchema_fails

/-! ## 6. Checks and axiom audit -/

#check S2007RepresentableFiberSubsingleton
#check S2007Subsingleton_of_stackEquiv
#check S2007SourceRepresentable
#check S2007CoverFiberDiscrete_of_sourceRepresentable
#check S2007CoverFiberDiscrete_of_quasiEquiv
#check S2007CoverFiberDiscrete_of_coneEssSurj
#check S2007BaseChangeFull
#check S2007BaseChangeFullAll
#check S2007BaseChangeSquare
#check S2007AllBaseChangesFull
#check S2007AllBaseChangesFull_implies_identity
#check S2007UniqFirstMissing_of_allBaseChangesFull
#check S2007SourceRepresentable_iff
#check S2007FirstMissing
#check S2007FirstMissing_iff_full
#check S2007FirstMissing_sourceRepresentable
#check S2007UniqFirstMissing_of_firstMissing
#check S2007UniqFirstMissing_of_full
#check S2007RecordedWitnessInsufficient
#check S2007EnlargedPresentationFails
#check S2007RepresentableSchemaFails

#print axioms S2007RepresentableFiberSubsingleton
#print axioms S2007Subsingleton_of_stackEquiv
#print axioms S2007CoverFiberDiscrete_of_sourceRepresentable
#print axioms S2007CoverFiberDiscrete_of_coneEssSurj
#print axioms S2007FirstMissing_iff_full
#print axioms S2007UniqFirstMissing_of_firstMissing
#print axioms S2007UniqFirstMissing_of_full
#print axioms S2007AllBaseChangesFull_implies_identity
#print axioms S2007UniqFirstMissing_of_allBaseChangesFull
#print axioms S2007RecordedWitnessInsufficient
#print axioms S2007EnlargedPresentationFails
#print axioms S2007RepresentableSchemaFails

end LeanFormal.IUT.XiFPaper.S2007CoverFiberDiscreteActual