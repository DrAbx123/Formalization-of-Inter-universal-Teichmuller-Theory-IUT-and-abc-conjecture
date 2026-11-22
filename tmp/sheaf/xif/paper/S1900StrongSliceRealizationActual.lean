/-
# S1900: strong slice realisation — the on-the-nose form and the representable case

## What this file decides

S1871 isolated the exact first missing for essential surjectivity of the coherent
covers as *slice realisation*

    S1871StrongSliceEquiv :  forall weak A, there is a strong finite-etale map
      f' : S' -> X and a 2-equivalence A.source ~= S' with f' ; (equivalence)
      ~= A.map.

and proved S1871EssSurj <-> S1871StrongSliceEquiv.  It left open the transport
S1871StrongTransfer from a cover isomorphism to a strong structure on the
*given* structure map, and therefore left open the on-the-nose form
S1871StrongRealization.

This file settles the presentation-level part of that transport and records
precisely what remains:

1. **Strongness is invariant under a 2-isomorphism of the structure map**
   (S1900StrongOfMapIso): a base-change presentation can be moved along an
   isomorphism f ~= f' of strong transformations with the same source and
   target.  The square of the presentation only changes in its comparison
   2-cell; a cone over the moved square is obtained from a cone over the original
   one by adjusting the comparison, and every field of the two-pullback witness,
   including the triangle identities and 2-cell extensionality, is the *same
   term* evaluated at the adjusted cone.  No strong presentation is fabricated:
   the old witness is reused verbatim.

2. **Hence S1871StrongInSlice <-> S1871StrongRealization**
   (S1900StrongInSlice_iff_strongRealization): realising the strong structure
   on the given map is the same as realising it on a 2-isomorphic map with the
   same source.  In particular the strictly stronger presentation-level input
   that S1866 showed to be *false* for the recorded (doubled) presentation,
   S1866StrongCoverOf, is not what is missing: the on-the-nose form does not
   ask the recorded presentations to be strong.

3. **The affine-model route to slice realisation, and why it cannot be the
   global answer.**  The affine model P_A of a cover with its finite-etale
   structure morphism pi_A : P_A -> Spec R' gives a *representable* map
   y(pi_A) : y(P_A) -> X whose strong base-change presentation **at the
   identity test point** is constructed unconditionally
   (S1900ModelTriangle_coneEssSurj): the square is the triangle
   y(P_A) -> y(P_A) -> X with apex P_A, and a cone's lift is its first leg.
   Given in addition that A.source is 2-equivalent to its affine model
   (S1743SourceRepresentable A), the S1743 lift/retraction data produce
   S1871StrongSliceEquivAt A (S1900StrongSliceEquivAt_of_model).
   But source representability is **refuted** in the tree:
   S1900NotSourceRepresentableAll : not S1743SourceRepresentableAll
   (S1850's doubled presentation has no retraction).  So the model route is
   intrinsically cover-dependent and cannot prove the global statement; the
   remaining input is *not* a representability statement about the model.

4. **The recorded-presentation strengthening is refuted, not missing.**
   S1900NotRecordedStrong: no strong structure forgets to S1850's doubled
   presentation (S1852), although the doubled cover *is* in the essential image
   (S1871).  So the missing input is a property of the *map*, not of the recorded
   base-change datum.

## The exact status of the first missing

* Proved here: S1871StrongRealization -> S1871StrongInSlice -> S1871EssSurj,
  and S1871StrongInSlice <-> S1871StrongRealization.
* Not proved here: the passage from a slice realisation of A (with a possibly
  different source) to a strong structure on A.map itself.  The case of a
  2-isomorphism of the structure map *with the same source* is proved in
  Section 1; in the source-equivalence case the two triangle identities of the
  transported two-pullback witness do not follow from the old witness, because
  whiskering the comparison 2-cells with the source equivalence is only a
  2-isomorphism and the target hom-category is no longer discrete.  This is
  recorded as S1900SourceTransport, and S1900EssSurj_iff_firstMissing shows that
  it is *exactly* the remaining step.  No axiom, no sorry, no fake strong
  presentation.

## References

S1726 (orbicurve stack), S1733 (affine model), S1742 (2-Yoneda comparison),
S1743 (lift and projection of the identity-point base change), S1756 (bicategorical
2-isomorphism calculus), S1762 (2-cell uniqueness for representable targets),
S1850 (doubled presentation, not S1743SourceRetraction), S1852 (S1852ConeEssSurj,
strong presentations), S1866 (coherence is presentation-level), S1871
(S1871EssSurj <-> S1871StrongSliceEquiv).
-/

import tmp.sheaf.xif.paper.S1871CoherentEssSurjActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1900StrongSliceRealizationActual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1871CoherentEssSurjActual

universe u

/-! ## 1. Moving a base-change presentation along a 2-isomorphism of the map -/

section MapIso

variable {source : EtaleStackOverField S1726K}
  {f f' : source.Hom S1726Orbicurve.stack}
  {testScheme : SchemeOverField S1726K}
  {point : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K testScheme)
    S1726Orbicurve.stack.fiber}

/-- The square of a base-change presentation, moved along e : f ~= f'.  Only the
comparison 2-cell changes. -/
noncomputable def S1900SquareOfMapIso
    (P : EtaleStackBaseChangePresentation f testScheme point) (e : Iso f f') :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K P.pullbackScheme)
      source.fiber
      (schemeRepresentableEtalePseudofunctor S1726K testScheme)
      S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk P.toSource P.projectionMap.transformation f' point
    ((S1756WhiskerLeftIso P.toSource f f' e).symm.trans P.commutes)

/-- A cone over the moved square is a cone over the original square with the
comparison 2-cell adjusted by e. -/
noncomputable def S1900ConeOfMapIso
    (P : EtaleStackBaseChangePresentation f testScheme point) (e : Iso f f')
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1900SquareOfMapIso P e).Cone W) :
    (S1852WeakSquare P).Cone W where
  toX := c.toX
  toY := c.toY
  commutes := (S1756WhiskerLeftIso c.toX f' f e.symm).symm.trans c.commutes

/-- A cone morphism over the moved square is a cone morphism over the original
square.  Its compatibility equation lives in the 2-cells into the orbicurve
stack, which are subsingletons because the orbicurve stack is representable. -/
noncomputable def S1900ConeMorphismOfMapIso
    (P : EtaleStackBaseChangePresentation f testScheme point) (e : Iso f f')
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S1900SquareOfMapIso P e).Cone W}
    (m : (S1900SquareOfMapIso P e).ConeMorphism s t) :
    (S1852WeakSquare P).ConeMorphism (S1900ConeOfMapIso P e s)
      (S1900ConeOfMapIso P e t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    haveI : Subsingleton
        (Pseudofunctor.StrongTrans.vcomp (S1900ConeOfMapIso P e s).toX
            (S1852WeakSquare P).xToBase ⟶
          Pseudofunctor.StrongTrans.vcomp (S1900ConeOfMapIso P e t).toY
            (S1852WeakSquare P).yToBase) :=
      S1762Modification_subsingleton_stack _ _
    exact Subsingleton.elim _ _

/-- The two-pullback witness of the moved square: every field is the original
field evaluated at the adjusted cone. -/
noncomputable def S1900WitnessOfMapIso
    (P : EtaleStackBaseChangePresentation f testScheme point) (e : Iso f f') :
    (S1900SquareOfMapIso P e).TwoPullbackWitness where
  lift W c := P.isPullback.lift W (S1900ConeOfMapIso P e c)
  liftToX W c := P.isPullback.liftToX W (S1900ConeOfMapIso P e c)
  liftToY W c := P.isPullback.liftToY W (S1900ConeOfMapIso P e c)
  liftTwoCell W s t m :=
    P.isPullback.liftTwoCell W (S1900ConeOfMapIso P e s)
      (S1900ConeOfMapIso P e t) (S1900ConeMorphismOfMapIso P e m)
  liftTwoCell_toX W s t m :=
    P.isPullback.liftTwoCell_toX W (S1900ConeOfMapIso P e s)
      (S1900ConeOfMapIso P e t) (S1900ConeMorphismOfMapIso P e m)
  liftTwoCell_toY W s t m :=
    P.isPullback.liftTwoCell_toY W (S1900ConeOfMapIso P e s)
      (S1900ConeOfMapIso P e t) (S1900ConeMorphismOfMapIso P e m)
  twoCell_ext W first second alpha beta h1 h2 :=
    P.isPullback.twoCell_ext W alpha beta h1 h2

/-- The base-change presentation of f' obtained by moving the presentation of f
along e.  The pullback scheme, the projection and the comparison to the source
are unchanged; only the comparison 2-cell is moved. -/
noncomputable def S1900PresentationOfMapIso
    (P : EtaleStackBaseChangePresentation f testScheme point) (e : Iso f f') :
    EtaleStackBaseChangePresentation f' testScheme point where
  pullbackScheme := P.pullbackScheme
  projection := P.projection
  projectionMap := P.projectionMap
  toSource := P.toSource
  commutes := (S1756WhiskerLeftIso P.toSource f f' e).symm.trans P.commutes
  isPullback := S1900WitnessOfMapIso P e

/-- **The full 2-universal property moves across a 2-isomorphism of the map.** -/
theorem S1900ConeEssSurj_of_mapIso
    (P : EtaleStackBaseChangePresentation f testScheme point) (e : Iso f f')
    (h : S1852ConeEssSurj P) :
    S1852ConeEssSurj (S1900PresentationOfMapIso P e) := by
  intro W c g hX hY
  exact h W (S1900ConeOfMapIso P e c) g hX hY

/-- **Strongness is invariant under a 2-isomorphism of the structure map.**  A
strong finite-etale structure can be moved along any isomorphism of strong
transformations with the same source and target. -/
noncomputable def S1900StrongOfMapIso
    (M : StrongEtaleStackFiniteEtaleMorphism f) (e : Iso f f') :
    StrongEtaleStackFiniteEtaleMorphism f' where
  baseChange testScheme point :=
    { toWeak := S1900PresentationOfMapIso (M.baseChange testScheme point).toWeak e
      coneEssSurj :=
        S1900ConeEssSurj_of_mapIso (M.baseChange testScheme point).toWeak e
          (M.baseChange testScheme point).coneEssSurj }
  hasProperty testScheme point := M.hasProperty testScheme point

/-- Strong realisation with the source fixed implies the on-the-nose form. -/
theorem S1900StrongRealization_of_strongInSlice (h : S1871StrongInSlice) :
    S1871StrongRealization := by
  intro A
  obtain ⟨f', ⟨M⟩, ⟨e⟩⟩ := h A
  exact ⟨S1900StrongOfMapIso M e⟩

/-- **The on-the-nose form and the fixed-source form of the missing input agree.**
S1871's S1871StrongInSlice asks for the strong structure on a map 2-isomorphic
to A.map with the same source; S1871StrongRealization asks for it on A.map
itself.  By the transport above the two are the same statement. -/
theorem S1900StrongInSlice_iff_strongRealization :
    S1871StrongInSlice ↔ S1871StrongRealization :=
  ⟨S1900StrongRealization_of_strongInSlice, S1871StrongInSlice_of_strongRealization⟩

/-- The pointwise form of the previous equivalence. -/
theorem S1900StrongInSliceAt_iff_strongRealizationAt (A : S1728Cover) :
    S1871StrongInSliceAt A ↔
      Nonempty (StrongEtaleStackFiniteEtaleMorphism A.map) := by
  constructor
  · rintro ⟨f', ⟨M⟩, ⟨e⟩⟩
    exact ⟨S1900StrongOfMapIso M e⟩
  · intro h
    exact ⟨A.map, h, ⟨Iso.refl A.map⟩⟩

end MapIso

/-! ## 2. The on-the-nose missing input suffices for essential surjectivity -/

/-- **The sharpened sufficient target**: every weak cover's structure map itself
carries a strong finite-etale structure, with no change of source.  This is the
on-the-nose form of the strong slice realisation of S1871. -/
def S1900FirstMissing : Prop := S1871StrongRealization

/-- The on-the-nose missing input is the fixed-source form of S1871's missing
statement. -/
theorem S1900FirstMissing_iff_strongInSlice :
    S1900FirstMissing ↔ S1871StrongInSlice :=
  S1900StrongInSlice_iff_strongRealization.symm

/-- **The on-the-nose missing input suffices for essential surjectivity.** -/
theorem S1900EssSurj_of_firstMissing (h : S1900FirstMissing) : S1871EssSurj :=
  S1871EssSurj_of_strongRealization h

/-- Equivalently, it suffices for strong slice realisation. -/
theorem S1900StrongSliceEquiv_of_firstMissing (h : S1900FirstMissing) :
    S1871StrongSliceEquiv :=
  S1871StrongSliceEquiv_of_strongInSlice (S1900FirstMissing_iff_strongInSlice.mp h)

/-- **The exact remaining step**: strongness of a structure map is invariant under
an isomorphism of covers, i.e. under a 2-equivalence of the source together with
the comparison of the structure maps.  This is S1871's S1871StrongTransfer. -/
def S1900SourceTransport : Prop := S1871StrongTransfer

/-- Given the source transport, essential surjectivity is *exactly* the
on-the-nose missing input: every weak cover's structure map carries a strong
finite-etale structure. -/
theorem S1900EssSurj_iff_firstMissing (h : S1900SourceTransport) :
    S1871EssSurj ↔ S1900FirstMissing :=
  S1871EssSurj_iff_strongRealization h
/-! ## 3. The affine-model route and its exact scope -/

section Model

/-- **Every representable etale pseudofunctor over the S1726 base is an etale
stack.**  This is the discrete-descent bridge of S1419 (a sheaf of types gives a
stack for its discrete-category pseudofunctor) plus subcanonicality of the etale
topology; S1726 recorded the case of the affine model only. -/
theorem S1900RepresentableIsStack (T : SchemeOverField S1726K) :
    (schemeRepresentableEtalePseudofunctor S1726K T).IsStack
      (SchemeOverField.etaleTopology S1726K) := by
  have hP : Presieve.IsSheaf (SchemeOverField.etaleTopology S1726K)
      (yoneda.obj T) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed.representableEtalePresheaf_isSheaf
        (F := S1726K) T)
  change (LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.discretePseudo
    (C := SchemeOverField S1726K) (yoneda.obj T)).IsStack
      (SchemeOverField.etaleTopology S1726K)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj T) hP

/-- The source stack of the affine-model cover of a weak cover: the representable
etale stack of the identity-point base-change model. -/
noncomputable def S1900ModelStack (A : S1728Cover) : EtaleStackOverField S1726K where
  fiber := S1743ModelStack A
  isStack := S1900RepresentableIsStack (S1733Model A)

@[simp] theorem S1900ModelStack_fiber (A : S1728Cover) :
    (S1900ModelStack A).fiber = S1743ModelStack A := rfl

/-- **The representable finite-etale structure map of the affine model**: the
Yoneda image of the finite-etale structure morphism
pi_A : S1733Model A -> Spec R' of the identity-point base change. -/
noncomputable def S1900ModelMap (A : S1728Cover) :
    (S1900ModelStack A).Hom S1726Orbicurve.stack :=
  S1742StrongTransOfHom (F := S1726K) (S1756Projection A)

/-- **The strong structure on the representable model map**, with no change of
source: this is the input the affine-model construction needs at a cover. -/
def S1900ModelStrongAt (A : S1728Cover) : Prop :=
  Nonempty (StrongEtaleStackFiniteEtaleMorphism (S1900ModelMap A))

/-- The global model-strongness statement: the representable finite-etale
structure map of every affine model carries strong base-change presentations at
every test point.  This is the "representable two-pullback" input. -/
def S1900ModelStrong : Prop := ∀ A : S1728Cover, S1900ModelStrongAt A

/-- The recorded projection map of the identity-point presentation is
2-isomorphic to the Yoneda image of the scheme morphism. -/
theorem S1900YonedaEval_modelMap (A : S1728Cover) :
    S1743YonedaEval (S1733Model A) S1726AffineOver (S1900ModelMap A) =
      S1756Projection A := by
  have h : (S1900ModelMap A : Pseudofunctor.StrongTrans
      (S1742YS (S1733Model A)) (S1742YS S1726AffineOver)) =
      S1742StrongTransOfHom (F := S1726K) (S1756Projection A) := rfl
  rw [h, S1743YonedaEval_eq_S1742, S1742HomOfStrongTrans_strongTransOfHom]

theorem S1900ProjectionMap_iso_modelMap (A : S1728Cover) :
    Nonempty (Iso (S1756ProjectionMap A) (S1900ModelMap A)) := by
  refine S1756IsoOfEvalEq (S1733Model A) S1726AffineOver _ _ ?_
  rw [S1756YonedaEval_projectionMap, S1900YonedaEval_modelMap]

/-- The strong structure on the representable model map gives one on the recorded
projection map, by the map-isomorphism transport of Section 1. -/
theorem S1900ProjectionMap_strong_of_model (A : S1728Cover)
    (h : S1900ModelStrongAt A) :
    Nonempty (StrongEtaleStackFiniteEtaleMorphism
      (source := S1900ModelStack A) (target := S1726Orbicurve.stack)
      (S1756ProjectionMap A)) := by
  obtain ⟨M⟩ := h
  obtain ⟨e⟩ := S1900ProjectionMap_iso_modelMap A
  exact ⟨S1900StrongOfMapIso M e.symm⟩

/-- The triangle square of the affine-model map at the identity test point. -/
noncomputable def S1900ModelTriangleSquare (A : S1728Cover) :
    EtalePseudofunctorSquare (S1900ModelStack A).fiber (S1900ModelStack A).fiber
      (S1743Y S1726AffineOver) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (Pseudofunctor.StrongTrans.id (S1900ModelStack A).fiber)
    (S1900ModelMap A) (S1900ModelMap A) S1733BasePoint
    ((S1756LeftUnitorIso (S1900ModelMap A)).trans
      (S1756RightUnitorIso (S1900ModelMap A)).symm)

/-- **The triangle square of the affine model is a bicategorical pullback.**  The
apex is the model itself, both horizontal maps are the model's structure map and
the two vertical maps are the identity and the identity point; a cone's lift is
its first leg.  The three coherence fields are equalities of 2-cells into a
representable stack, hence subsingleton (S1762). -/
noncomputable def S1900ModelTriangleWitness (A : S1728Cover) :
    (S1900ModelTriangleSquare A).TwoPullbackWitness where
  lift W cone := cone.toX
  liftToX W cone := S1756RightUnitorIso cone.toX
  liftToY W cone := cone.commutes.trans (S1756RightUnitorIso cone.toY)
  liftTwoCell W source target morphism := morphism.toX
  liftTwoCell_toX := by
    intro W source target morphism
    haveI : Subsingleton
        (Pseudofunctor.StrongTrans.vcomp source.toX (S1900ModelTriangleSquare A).toX ⟶
          Pseudofunctor.StrongTrans.vcomp target.toX (S1900ModelTriangleSquare A).toX) :=
      S1762Modification_subsingleton_representable (S := S1733Model A) _ _
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target morphism
    haveI : Subsingleton
        (Pseudofunctor.StrongTrans.vcomp source.toX (S1900ModelTriangleSquare A).toY ⟶
          Pseudofunctor.StrongTrans.vcomp target.toX (S1900ModelTriangleSquare A).toY) :=
      S1762Modification_subsingleton_representable (S := S1726AffineOver) _ _
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    haveI : Subsingleton (first ⟶ second) :=
      S1762Modification_subsingleton_representable (S := S1733Model A) first second
    exact Subsingleton.elim _ _

/-- **The identity-point base-change presentation of the representable model map.**
The pullback scheme is the affine model, the projection is its finite-etale
structure morphism and the square is the triangle square. -/
noncomputable def S1900ModelTrianglePresentation (A : S1728Cover) :
    EtaleStackBaseChangePresentation (S1900ModelMap A) S1726AffineOver S1733BasePoint where
  pullbackScheme := S1733Model A
  projection := S1756Projection A
  projectionMap :=
    { transformation := S1900ModelMap A
      app_eq := fun _ => rfl }
  toSource := Pseudofunctor.StrongTrans.id (S1900ModelStack A).fiber
  commutes :=
    (S1756LeftUnitorIso (S1900ModelMap A)).trans
      (S1756RightUnitorIso (S1900ModelMap A)).symm
  isPullback := S1900ModelTriangleWitness A

/-- **The strong base-change presentation of the representable finite-etale model
map at the identity test point, unconditionally.**  Any 1-cell into the model
whose first projection is 2-isomorphic to the cone's first leg is 2-isomorphic to
the cone's lift, because the first projection is the identity. -/
theorem S1900ModelTriangle_coneEssSurj (A : S1728Cover) :
    S1852ConeEssSurj (S1900ModelTrianglePresentation A) := by
  intro W c f hX hY
  obtain ⟨eX⟩ := hX
  exact ⟨(S1756RightUnitorIso f).symm.trans eX⟩

/-- The representable finite-etale structure map of the affine model carries a
strong base-change presentation at the identity test point. -/
theorem S1900ModelIdentityPointStrong (A : S1728Cover) :
    ∃ P : EtaleStackBaseChangePresentation (S1900ModelMap A) S1726AffineOver S1733BasePoint,
      S1852ConeEssSurj P :=
  ⟨S1900ModelTrianglePresentation A, S1900ModelTriangle_coneEssSurj A⟩

/-- **The affine-model route, per cover.**  If the source of a cover is
2-equivalent to its affine model and the model's representable structure map is
strong, then the cover satisfies S1871's strong slice realisation.  The
2-equivalence is the pair (S1743Lift A, toSource) supplied by the identity-point
base change; its unit is the two-pullback comparison and its counit is the
retraction hypothesis. -/
theorem S1900StrongSliceEquivAt_of_model (A : S1728Cover)
    (hSrc : S1743SourceRepresentable A) (hM : S1900ModelStrongAt A) :
    S1871StrongSliceEquivAt A := by
  obtain ⟨M⟩ := hM
  obtain ⟨M'⟩ := S1900ProjectionMap_strong_of_model A ⟨M⟩
  obtain ⟨inv, ⟨hu1inv⟩, ⟨hu2inv⟩⟩ := hSrc
  have hproj : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1900ModelMap A)) A.map) := by
    obtain ⟨e⟩ := S1900ProjectionMap_iso_modelMap A
    obtain ⟨e2⟩ := S1743Lift_projection A
    exact ⟨(S1756WhiskerLeftIso (S1743Lift A) (S1756ProjectionMap A)
      (S1900ModelMap A) e).symm.trans e2⟩
  refine ⟨S1900ModelStack A, S1900ModelMap A, S1743Lift A, S1756ToSource A,
    ⟨M⟩, ?_, ?_, hproj⟩
  · exact ⟨(S1743BaseChange A).isPullback.liftToX (S1743Source A)
      (S1743IdentityCone A)⟩
  · exact ⟨S1756_unit_iso (S1756ToSource A) (S1743Lift A) inv
      ((S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A))
      hu2inv⟩

/-- **The affine-model route is not a global route**: the source of an arbitrary
cover is *not* in general 2-equivalent to its affine model.  S1850's doubled
presentation has no retraction, since its identity-point self-endomorphism is
fold ; inl, not the identity. -/
theorem S1900NotSourceRepresentableAll : ¬ S1743SourceRepresentableAll :=
  fun h => S1850_not_sourceRetraction (S1743SourceRetraction_of_representable h)

/-- **The recorded-presentation strengthening is refuted.**  No strong
finite-etale structure forgets to S1850's doubled presentation of the identity
map (S1852), although the doubled cover *is* in the essential image of the
coherent covers (S1871).  Hence the missing input cannot be a condition on the
recorded base-change presentations. -/
theorem S1900NotRecordedStrong :
    ¬ ∃ M : StrongEtaleStackFiniteEtaleMorphism
        (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber),
      M.toWeak = S1850DoubledFiniteEtale :=
  S1852Doubled_not_strong

/-- The same statement as a negation of the presentation-level coherence
condition of S1866 on all covers: some recorded cover has no strong refinement of
its recorded structure. -/
theorem S1900NotAllRecordedStrong :
    ¬ (∀ A : S1728Cover, ∃ M : StrongEtaleStackFiniteEtaleMorphism A.map,
        M.toWeak = A.finiteEtale) := by
  intro h
  obtain ⟨M, hM⟩ := h S1850DoubledCover
  exact S1900NotRecordedStrong ⟨M, hM⟩

end Model
/-! ## 4. Non-vacuity: the doubled cover satisfies the on-the-nose form -/

/-- The structure map of S1850's doubled cover carries a strong finite-etale
structure, namely the identity's.  Hence the on-the-nose missing input is
satisfied by the very cover whose recorded presentation refutes the
presentation-level condition: the two statements are genuinely different. -/
theorem S1900StrongRealizationAt_doubled :
    Nonempty (StrongEtaleStackFiniteEtaleMorphism S1850DoubledCover.map) :=
  ⟨S1852IdStrong⟩

/-- The same for the terminal coherent cover. -/
theorem S1900StrongRealizationAt_terminal :
    Nonempty (StrongEtaleStackFiniteEtaleMorphism S1852TerminalCoherent.cover.map) :=
  ⟨S1852TerminalCoherent.toStrongCover.finiteEtale⟩

/-- **Diagnosis.**  The affine-model route is provably not a global route (source
representability is refuted), the recorded-presentation refinement is refuted,
the on-the-nose form of the missing input is satisfied by the doubled cover, is
equivalent to S1871's fixed-source realisation, and suffices for essential
surjectivity. -/
theorem S1900Diagnosis :
    (¬ S1743SourceRepresentableAll) ∧
      (¬ ∃ M : StrongEtaleStackFiniteEtaleMorphism
          (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber),
        M.toWeak = S1850DoubledFiniteEtale) ∧
      Nonempty (StrongEtaleStackFiniteEtaleMorphism S1850DoubledCover.map) ∧
      (S1900FirstMissing ↔ S1871StrongInSlice) ∧
      (S1900FirstMissing → S1871EssSurj) :=
  ⟨S1900NotSourceRepresentableAll, S1900NotRecordedStrong,
    S1900StrongRealizationAt_doubled, S1900FirstMissing_iff_strongInSlice,
    S1900EssSurj_of_firstMissing⟩

section Consumer

open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
attribute [local instance] S1854CoherentCategory11

/-- **Consumer: the coherent-cover forgetful functor is essentially surjective.**
The on-the-nose missing input makes the forgetful functor from the coherent
covers to the S1728 2-isomorphism category essentially surjective (S1871's
reformulation of essential surjectivity). -/
theorem S1900ForgetEssSurj_of_firstMissing (h : S1900FirstMissing) :
    S1854Forget11.EssSurj :=
  S1871EssSurj_iff_forget_essSurj.mp (S1900EssSurj_of_firstMissing h)

end Consumer

/-! ## 5. Checks and axiom audit -/

#check S1900SquareOfMapIso
#check S1900ConeOfMapIso
#check S1900ConeMorphismOfMapIso
#check S1900WitnessOfMapIso
#check S1900PresentationOfMapIso
#check S1900ConeEssSurj_of_mapIso
#check S1900StrongOfMapIso
#check S1900StrongRealization_of_strongInSlice
#check S1900StrongInSlice_iff_strongRealization
#check S1900StrongInSliceAt_iff_strongRealizationAt
#check S1900FirstMissing
#check S1900FirstMissing_iff_strongInSlice
#check S1900EssSurj_of_firstMissing
#check S1900StrongSliceEquiv_of_firstMissing
#check S1900SourceTransport
#check S1900EssSurj_iff_firstMissing
#check S1900RepresentableIsStack
#check S1900ModelStack
#check S1900ModelMap
#check S1900ModelStrongAt
#check S1900ModelStrong
#check S1900YonedaEval_modelMap
#check S1900ProjectionMap_iso_modelMap
#check S1900ProjectionMap_strong_of_model
#check S1900ModelTriangleSquare
#check S1900ModelTriangleWitness
#check S1900ModelTrianglePresentation
#check S1900ModelTriangle_coneEssSurj
#check S1900ModelIdentityPointStrong
#check S1900StrongSliceEquivAt_of_model
#check S1900NotSourceRepresentableAll
#check S1900NotRecordedStrong
#check S1900NotAllRecordedStrong
#check S1900StrongRealizationAt_doubled
#check S1900StrongRealizationAt_terminal
#check S1900Diagnosis
#check S1900ForgetEssSurj_of_firstMissing

#print axioms S1900ConeEssSurj_of_mapIso
#print axioms S1900StrongOfMapIso
#print axioms S1900StrongInSlice_iff_strongRealization
#print axioms S1900EssSurj_of_firstMissing
#print axioms S1900EssSurj_iff_firstMissing
#print axioms S1900RepresentableIsStack
#print axioms S1900ModelTriangle_coneEssSurj
#print axioms S1900ModelIdentityPointStrong
#print axioms S1900StrongSliceEquivAt_of_model
#print axioms S1900NotSourceRepresentableAll
#print axioms S1900NotRecordedStrong
#print axioms S1900NotAllRecordedStrong
#print axioms S1900StrongRealizationAt_doubled
#print axioms S1900Diagnosis
#print axioms S1900ForgetEssSurj_of_firstMissing

end LeanFormal.IUT.XiFPaper.S1900StrongSliceRealizationActual