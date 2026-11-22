/-
# S1899: the coherent strong pullback/coproduct apex --- construction targets,
  the choice-free reduction, and the exact geometric first missing

## The question

S1854/S1856 reduced the pullback and finite-coproduct structures of the coherent
category to the apex-coherence conditions

  S1854PullbackApexCoherent h          (the *chosen* Limits.pullback apex is a
                                        coherent cover),
  S1854CoproductApexCoherent h0 h2     (the *chosen* bottom and binary coproduct
                                        apexes are coherent covers),

and S1866 proved that these are equivalent to the strongness, at every test point
`(T, q)`, of the recorded base-change presentations of the chosen apex
(`S1852ConeEssSurj`), and that they are *not* consequences of the weak datum
plus the two-pullback universal property: coherence is a property of the recorded
presentation and is not invariant under isomorphism of covers.

The task is therefore: for every cospan of coherent covers, construct the
geometric fibre product (and the initial object and the binary coproducts) so
that the chosen base-change presentations are strong, or else name the exact
first missing.  The hint is to use the S1804 iso-comma, the S1852 strong
presentation, and the S1762 terminal cover.

## Verdict

The geometric fibre product is not constructed here.  What is done is:

1. **The choice-free target.**  `S1899PullbackApexPresentationsStrong` is the
   task's exact phrasing: for every cospan of coherent covers there is a
   two-pullback datum `P` (S1832) whose apex's recorded presentations satisfy
   `S1852ConeEssSurj` at *all* `(T, q)`.  It is proved equivalent to
   `S1899TwoPullbackApexStrongAll`, the existence of a two-pullback datum whose
   apex is literally the underlying cover of a coherent cover
   (`S1866StrongCoverOf`, by S1866's `..._iff_baseChange`).

2. **The target is the choice-free residue of the S1854/S1856 condition.**  The
   chosen-limit condition of S1866 (`S1866PullbackApexFirstMissing`) implies the
   choice-free target (`S1899Presentations_of_chosen`), while the converse needs
   control of the classical choice of `Limits.pullback`; the target is therefore
   the part of the condition that a construction can actually produce.
   `S1899ApexPresentationLoadBearing` makes the choice load-bearing: over the
   identity cospan of the terminal cover one two-pullback apex is the coherent
   terminal cover and another is S1850's non-coherent doubled cover.

3. **The target is sufficient for the coherent category.**  From
   `S1899TwoPullbackApexStrongAll` the full `HasPullbacks` on
   `S1854CoherentCategory11` is derived
   (`S1899HasPullbacks_of_twoPullbackApex`), by creating the actual S1728 limit
   cones in S1856's strict image subcategory.  No limit is fabricated.  The same
   is done for the initial object, the binary coproducts and finite coproducts
   (`S1899HasFiniteCoproducts`).

4. **The apex-coherence bottleneck is dissolved for the categorical structure.**
   Independently of any apex coherence, `HasPullbacks CoherentCover` is proved
   from the coherent affine bridge of S1878, i.e. from `S1878EssSurj`
   (`S1899HasPullbacks_of_essSurj`) --- the *same* missing input that S1865 uses
   for finite coproducts.  The transport uses the target's genuine
   `HasPullbacks (FiniteEtaleCover (Spec R'))`
   (`Example36.finiteEtaleCoverHasPullbacks`), pulled back along the
   equivalences `S1878Functor` and `S1865CoherentTo1854`.  This shows that
   S1854's chosen-apex condition is *not* needed for the categorical limits: only
   the geometric identification of the categorical pullback with the iso-comma is
   still missing.

5. **The exact first missing.**  The geometric construction is reduced to a
   single named statement, `S1899GeometricStrongIsoCommaAll`: for every cospan of
   coherent covers there is an S1864 iso-comma stack obligation `D` (itself
   S1864's four-part obligation: pseudofunctor comparisons, effective descent,
   representably finite-etale structure map, universal property) whose apex
   `D.apex` carries a strong finite-etale structure *refining the recorded weak
   presentations of the obligation* (`S1866StrongCoverOf D.apex`).  This
   statement implies the target (`S1899TwoPullbackApexStrongAll_of_geometric`).
   Its components are not available in the tree: the pseudofunctor comparisons are
   not in Mathlib (S1864), effective descent for the pointwise two-fibre product
   is S1891's named descent theorem (`S1891StackTwoFiberProductDescent`), and the
   strong structure on the apex is the new presentation-level input.  In
   particular the weak obligation alone does not give it, because S1866's no-go
   shows that the strong structure is not recoverable from an isomorphic apex
   (S1850's doubled cover has the same source and structure map as the coherent
   terminal cover but is not coherent).

6. **Non-vacuity.**  The target is inhabited for all cospans with an identity leg
   (`S1899IdentityLegPullbackApex`), with the apex the other coherent cover and
   the datum S1832's unconditional identity-leg two-pullback.

## Honest boundary

No geometric fibre product, no iso-comma stack, no strong structure on a
pullback/coproduct apex and no descent theorem is constructed.  Every Prop with
no inhabitant is named explicitly and no sorry, axiom, `Shrink`, `ULift` or
`PUnit` occurs; only `propext`, `Classical.choice` and `Quot.sound` are
used (see the audit block).
-/

import tmp.sheaf.xif.paper.S1866ApexCoherenceActual
import tmp.sheaf.xif.paper.S1865CoprodApexActual
import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual
import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual
import tmp.sheaf.xif.paper.S1891PullbackStackIsStackActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1899CoherentStrongApexActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut

open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
open LeanFormal.IUT.XiFPaper.S1866ApexCoherenceActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual
open LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual

attribute [local instance] S1854CoherentCategory11

/-! ## 1. The choice-free coherent pullback apex -/

/-- **The choice-free coherent pullback apex for one cospan.**  There is a
bicategorical two-pullback datum (S1832) for the cospan of actual cover maps
whose apex is the underlying cover of a coherent cover, i.e. whose recorded
weak finite-etale structure admits a strong refinement with the same
base-change presentations. -/
def S1899TwoPullbackApexStrong {A B C : CoherentCover}
    (f : S1728CoverMap A.cover C.cover) (g : S1728CoverMap B.cover C.cover) : Prop :=
  ∃ P : S1832TwoPullback f g, S1866StrongCoverOf P.apex

/-- **The task's exact phrasing.**  For every cospan of coherent covers there is
a two-pullback datum whose apex's *chosen* base-change presentations are strong
at every test scheme and point: `S1852ConeEssSurj` for the recorded
`EtaleStackBaseChangePresentation` of the apex at all `(T, q)`. -/
def S1899PullbackApexPresentationsStrong : Prop :=
  ∀ (A B C : CoherentCover) (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover),
    ∃ P : S1832TwoPullback f g,
      ∀ (T : SchemeOverField S1726K)
        (q : Pseudofunctor.StrongTrans
          (schemeRepresentableEtalePseudofunctor S1726K T)
          S1726Orbicurve.stack.fiber),
        S1852ConeEssSurj (P.apex.finiteEtale.baseChange T q)

/-- The coherent-cover form of the target. -/
def S1899TwoPullbackApexStrongAll : Prop :=
  ∀ (A B C : CoherentCover) (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover),
    S1899TwoPullbackApexStrong f g

/-- **The target in its exact presentation-level form is the coherent-cover
form.**  This is S1866's characterisation of coherence as the strongness of
*every* recorded base change, applied to the chosen apex of the datum. -/
theorem S1899Presentations_iff_twoPullbackApex :
    S1899PullbackApexPresentationsStrong ↔ S1899TwoPullbackApexStrongAll := by
  constructor
  · intro h A B C f g
    obtain ⟨P, hP⟩ := h A B C f g
    exact ⟨P, (S1866StrongCoverOf_iff_baseChange P.apex).mpr hP⟩
  · intro h A B C f g
    obtain ⟨P, hP⟩ := h A B C f g
    exact ⟨P, (S1866StrongCoverOf_iff_baseChange P.apex).mp hP⟩

/-- A coherent cover whose underlying cover is the apex, extracted from the
strongness of the recorded presentation. -/
theorem S1899CoherentCoverOfStrong {Y : S1728Cover} (h : S1866StrongCoverOf Y) :
    ∃ P : CoherentCover, P.cover = Y :=
  (S1866StrongCoverOf_iff_coherent Y).mp h

/-! ## 2. The target implies the categorical limits on the coherent covers -/

/-- **The strict image of the coherent covers has all pullbacks, from coherent
two-pullback apexes.**  For a cospan in S1856's strict image subcategory, S1832
turns the coherent two-pullback datum into an actual limit cone of the cospan in
the S1728 cover category; its apex is in the strict image by construction, so
the full-subcategory inclusion creates the limit.  This is the unconditional
limit half of the construction; nothing is fabricated. -/
theorem S1899HasPullbacksStrictSub (h : S1899TwoPullbackApexStrongAll) :
    HasPullbacks S1856StrictSub := by
  haveI : ∀ {X Y Z : S1856StrictSub} {f : X ⟶ Z} {g : Y ⟶ Z},
      HasLimit (cospan f g) := by
    intro X Y Z f g
    rcases X with ⟨X0, ⟨A, hAX⟩⟩
    rcases Y with ⟨Y0, ⟨B, hBY⟩⟩
    rcases Z with ⟨Z0, ⟨C, hCZ⟩⟩
    subst hAX
    subst hBY
    subst hCZ
    obtain ⟨P, hP⟩ := h A B C (Quot.out f.hom) (Quot.out g.hom)
    have hPc : IsLimit (S1832PullbackCone P) := S1832PullbackConeIsLimit P
    have hdiag : cospan (S1832Q (Quot.out f.hom)) (S1832Q (Quot.out g.hom)) =
        cospan f.hom g.hom := by
      rw [S1832Q_out f.hom, S1832Q_out g.hom]
    let c : PullbackCone f.hom g.hom :=
      (Cone.postcompose (eqToIso hdiag.symm).inv).obj (S1832PullbackCone P)
    have hc : IsLimit c :=
      (IsLimit.postcomposeInvEquiv (eqToIso hdiag.symm) (S1832PullbackCone P)).symm hPc
    let alpha := cospanCompIso S1856StrictProperty.ι f g
    let c0 : Cone ((cospan f g) ⋙ S1856StrictProperty.ι) := (Cone.postcompose alpha.inv).obj c
    have hc0 : IsLimit c0 := (IsLimit.postcomposeInvEquiv alpha c).symm hc
    have hQ : S1856StrictProperty c0.pt := by
      show S1856StrictProperty P.apex
      obtain ⟨Q, hQ⟩ := S1899CoherentCoverOfStrong hP
      exact ⟨Q, hQ⟩
    haveI hKl : HasLimit ((cospan f g) ⋙ S1856StrictProperty.ι) := HasLimit.mk ⟨c0, hc0⟩
    letI : CreatesLimit (cospan f g) S1856StrictProperty.ι :=
      createsLimitFullSubcategoryInclusion' (cospan f g) hc0 hQ
    exact hasLimit_of_created (cospan f g) S1856StrictProperty.ι
  exact @hasPullbacks_of_hasLimit_cospan S1856StrictSub _ this

/-- **The coherent category has pullbacks from the choice-free coherent
pullback apexes.**  The limits are transported across the equivalence
`S1856ToStrict : CoherentCover ⥤ S1856StrictSub`; no chosen `Limits.pullback`
of the S1728 category and no apex-coherence condition on it is used. -/
theorem S1899HasPullbacks_of_twoPullbackApex (h : S1899TwoPullbackApexStrongAll) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 :=
  @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    S1856StrictSub _ CoherentCover _ WalkingCospan _
    S1856ToStrict S1856ToStrict_isEquivalence (S1899HasPullbacksStrictSub h)

/-- The presentation-level form feeds the same theorem. -/
theorem S1899HasPullbacks_of_presentations (h : S1899PullbackApexPresentationsStrong) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 :=
  S1899HasPullbacks_of_twoPullbackApex (S1899Presentations_iff_twoPullbackApex.mp h)

/-! ## 3. The affine-bridge route: no apex coherence at all

The categorical structure does not need the geometric fibre product: the coherent
affine bridge of S1878 is an equivalence exactly when `S1878EssSurj` holds
(`S1878Functor_isEquivalence_iff_essSurj`), the affine target
`FiniteEtaleCover (Spec R')` has all pullbacks unconditionally
(`Example36.finiteEtaleCoverHasPullbacks`), and the coherent category is
equivalent to the induced category used in S1878 (`S1865CoherentTo1854`). -/

/-- **The affine target has all pullbacks.** -/
theorem S1899AffineTargetHasPullbacks : HasPullbacks S1878Target :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.finiteEtaleCoverHasPullbacks S1816Base

/-- **The coherent covers have all pullbacks from `S1878EssSurj`.**  This is a
completely different route from S1854/S1856: it never mentions the chosen S1728
pullback, so no apex-coherence condition occurs.  The only input is the
essential surjectivity of the coherent-cover affine comparison --- exactly the
same missing statement that S1865 uses for finite coproducts. -/
theorem S1899HasPullbacks_of_essSurj (h : S1878EssSurj) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 := by
  letI : S1878Functor.IsEquivalence := S1878Functor_isEquivalence_iff_essSurj.mpr h
  haveI hT : HasLimitsOfShape WalkingCospan S1878CoherentCategory :=
    @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      S1878Target _ S1878CoherentCategory _ WalkingCospan _
      S1878Functor inferInstance S1899AffineTargetHasPullbacks
  exact @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    S1878CoherentCategory _ CoherentCover _ WalkingCospan _
    S1865CoherentTo1854.asEquivalence.inverse
    (Equivalence.isEquivalence_inverse S1865CoherentTo1854.asEquivalence)
    hT

/-- The S1878 pair form (the shape used by S1865 and S1868). -/
theorem S1899HasPullbacks_of_bridge (h : S1878Full ∧ S1878EssSurj) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 :=
  S1899HasPullbacks_of_essSurj h.2

/-! ## 4. The geometric reduction: the iso-comma obligation with a strong
structure is sufficient -/

/-- **The geometric coherent pullback apex for one cospan.**  An S1864 iso-comma
stack obligation (site pseudofunctor, effective descent, the two projections,
the representably finite-etale structure map, the bicategorical universal
property) whose apex carries a strong finite-etale structure on exactly the
recorded weak presentations. -/
def S1899GeometricStrongIsoComma {A B C : CoherentCover}
    (f : S1728CoverMap A.cover C.cover) (g : S1728CoverMap B.cover C.cover) : Prop :=
  ∃ D : S1864IsoCommaStackObligation f g, S1866StrongCoverOf D.apex

/-- **The exact geometric first missing.**  For every cospan of coherent covers,
the geometric two-fibre product is constructed together with a strong structure
on its structure map. -/
def S1899GeometricStrongIsoCommaAll : Prop :=
  ∀ (A B C : CoherentCover) (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover), S1899GeometricStrongIsoComma f g

/-- The weak half of the geometric input, for the record: the iso-comma stack
obligation alone (S1864), whose structure map is only *recorded* as
representably finite etale. -/
def S1899IsoCommaObligationAll : Prop :=
  ∀ (A B C : CoherentCover) (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover),
    Nonempty (S1864IsoCommaStackObligation f g)

/-- **The geometric construction gives the choice-free target.**  The obligation
already contains the two-pullback datum
(`S1864IsoCommaStackObligation.toTwoPullback`) and its apex is strong by
hypothesis. -/
theorem S1899TwoPullbackApexStrongAll_of_geometric
    (h : S1899GeometricStrongIsoCommaAll) : S1899TwoPullbackApexStrongAll :=
  fun A B C f g => by
    obtain ⟨D, hD⟩ := h A B C f g
    exact ⟨D.toTwoPullback, hD⟩

/-- Hence the geometric construction gives the task's presentation-level target. -/
theorem S1899Presentations_of_geometric (h : S1899GeometricStrongIsoCommaAll) :
    S1899PullbackApexPresentationsStrong :=
  S1899Presentations_iff_twoPullbackApex.mpr
    (S1899TwoPullbackApexStrongAll_of_geometric h)

/-- Hence it gives pullbacks on the coherent category. -/
theorem S1899HasPullbacks_of_geometric (h : S1899GeometricStrongIsoCommaAll) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 :=
  S1899HasPullbacks_of_twoPullbackApex (S1899TwoPullbackApexStrongAll_of_geometric h)

/-- The geometric first missing is at least as strong as the weak iso-comma
obligation. -/
theorem S1899IsoCommaObligationAll_of_geometric (h : S1899GeometricStrongIsoCommaAll) :
    S1899IsoCommaObligationAll :=
  fun A B C f g => by
    obtain ⟨D, _⟩ := h A B C f g
    exact ⟨D⟩

/-! ## 5. The choice-free target is the residue of S1866's chosen-apex condition -/

/-- **S1866's chosen-apex condition implies the choice-free target.**  The chosen
limit's two-pullback datum (`S1832TwoPullbackOfHasPullback`) has the chosen
apex, and S1866's presentation-level condition supplies its strongness. -/
theorem S1899Presentations_of_chosen (h : HasPullbacks S1728Cover)
    (hA : S1866PullbackApexFirstMissing h) : S1899PullbackApexPresentationsStrong := by
  intro A B C f g
  letI := h
  refine ⟨S1832TwoPullbackOfHasPullback (inferInstance : HasPullback (S1832Q f) (S1832Q g)),
    fun T q => ?_⟩
  exact hA A B C (S1832Q f) (S1832Q g) T q

/-- S1866's condition also gives the coherent-cover form of the target. -/
theorem S1899TwoPullbackApexStrongAll_of_chosen (h : HasPullbacks S1728Cover)
    (hA : S1866PullbackApexFirstMissing h) : S1899TwoPullbackApexStrongAll :=
  S1899Presentations_iff_twoPullbackApex.mp (S1899Presentations_of_chosen h hA)

/-! ## 6. The coherent initial object and binary coproducts -/

/-- **The choice-free coherent initial apex.**  The chosen S1728 initial object
(of an arbitrary initial-object structure) is the underlying cover of a coherent
cover and is initial. -/
def S1899InitialApex : Prop :=
  ∃ P : CoherentCover, Nonempty (IsInitial P.cover)

/-- **The choice-free coherent binary-coproduct apex.**  For every pair of
coherent covers there is an actual binary-coproduct cofan whose point is the
underlying cover of a coherent cover. -/
def S1899BinaryCoproductApex : Prop :=
  ∀ A B : CoherentCover,
    ∃ (P : CoherentCover) (c : BinaryCofan A.cover B.cover),
      Nonempty (IsColimit c) ∧ c.pt = P.cover

/-- The two coproduct targets. -/
def S1899CoproductApex : Prop := S1899InitialApex ∧ S1899BinaryCoproductApex

/-- The strict image has an initial object from a coherent initial apex. -/
theorem S1899HasInitialStrictSub (h : S1899InitialApex) : HasInitial S1856StrictSub := by
  obtain ⟨P, ⟨hP⟩⟩ := h
  let Q : S1856StrictSub := ⟨P.cover, ⟨P, rfl⟩⟩
  have hQ : IsInitial Q := by
    refine IsInitial.ofUniqueHom (fun Y => ObjectProperty.homMk (hP.to Y.obj)) ?_
    intro Y m
    apply ObjectProperty.hom_ext
    exact hP.hom_ext m.hom (hP.to Y.obj)
  exact IsInitial.hasInitial hQ

/-- The strict image has binary coproducts from coherent coproduct apexes.  The
given cofan is transported to the diagram of the inclusion functor and the
full-subcategory inclusion creates the colimit because the point is in the
strict image. -/
theorem S1899HasBinaryCoproductsStrictSub (h : S1899BinaryCoproductApex) :
    HasBinaryCoproducts S1856StrictSub := by
  haveI : ∀ {X Y : S1856StrictSub}, HasColimit (pair X Y) := by
    intro X Y
    obtain ⟨A, hAX⟩ := X.property
    obtain ⟨B, hBY⟩ := Y.property
    obtain ⟨P, c, ⟨hc⟩, hpt⟩ := h A B
    let beta : pair X.obj Y.obj ≅ pair A.cover B.cover :=
      (mapPairIso (F := pair A.cover B.cover) (G := pair X.obj Y.obj)
        (eqToIso hAX) (eqToIso hBY)).symm
    let c1 : Cocone (pair X.obj Y.obj) := (Cocone.precompose beta.hom).obj c
    have hc1 : IsColimit c1 := (IsColimit.precomposeHomEquiv beta c).symm hc
    let alpha := pairComp X Y S1856StrictProperty.ι
    let c2 : Cocone ((pair X Y) ⋙ S1856StrictProperty.ι) :=
      (Cocone.precompose alpha.hom).obj c1
    have hc2 : IsColimit c2 := (IsColimit.precomposeHomEquiv alpha c1).symm hc1
    have hQ : S1856StrictProperty c2.pt := by
      show S1856StrictProperty c.pt
      rw [hpt]
      exact ⟨P, rfl⟩
    haveI hKl : HasColimit ((pair X Y) ⋙ S1856StrictProperty.ι) := HasColimit.mk ⟨c2, hc2⟩
    letI : CreatesColimit (pair X Y) S1856StrictProperty.ι :=
      createsColimitFullSubcategoryInclusion' (pair X Y) hc2 hQ
    exact hasColimit_of_created (pair X Y) S1856StrictProperty.ι
  exact @hasBinaryCoproducts_of_hasColimit_pair S1856StrictSub _ this

/-- **The coherent category has an initial object from the choice-free
coproduct apexes.** -/
theorem S1899HasInitial (h : S1899CoproductApex) :
    @HasInitial CoherentCover S1854CoherentCategory11 :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 S1856StrictSub _ (Discrete PEmpty) _
    S1856ToStrict S1856ToStrict_isEquivalence (S1899HasInitialStrictSub h.1)

/-- **The coherent category has binary coproducts from the choice-free
coproduct apexes.** -/
theorem S1899HasBinaryCoproducts (h : S1899CoproductApex) :
    @HasBinaryCoproducts CoherentCover S1854CoherentCategory11 :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 S1856StrictSub _ (Discrete WalkingPair) _
    S1856ToStrict S1856ToStrict_isEquivalence (S1899HasBinaryCoproductsStrictSub h.2)

/-- **The coherent category has finite coproducts from the choice-free
coproduct apexes.** -/
theorem S1899HasFiniteCoproducts (h : S1899CoproductApex) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 := by
  letI : @HasInitial CoherentCover S1854CoherentCategory11 := S1899HasInitial h
  letI : @HasBinaryCoproducts CoherentCover S1854CoherentCategory11 :=
    S1899HasBinaryCoproducts h
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-! ### 6b. The coproduct target from the existing presentation-level inputs -/

/-- **The chosen-coproduct condition of S1866 implies the choice-free
coproduct target.**  The chosen bottom and the chosen binary coproduct carry
strong presentations (`S1866CoproductApexFirstMissing`); the corresponding
cofans are the honest `coprodIsCoprod` cofans of those chosen objects. -/
theorem S1899CoproductApex_of_chosen (h0 : HasInitial S1728Cover)
    (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1866CoproductApexFirstMissing h0 h2) : S1899CoproductApex := by
  letI := h0
  letI := h2
  obtain ⟨hInit, hCop⟩ := hA
  constructor
  · obtain ⟨P, hP⟩ := S1899CoherentCoverOfStrong
      ((S1866StrongCoverOf_iff_baseChange (⊥_ S1728Cover)).mpr hInit)
    exact ⟨P, ⟨hP.symm ▸ initialIsInitial⟩⟩
  · intro A B
    obtain ⟨P, hP⟩ := S1899CoherentCoverOfStrong
      ((S1866StrongCoverOf_iff_baseChange (A.cover ⨿ B.cover)).mpr (hCop A B))
    exact ⟨P, BinaryCofan.mk coprod.inl coprod.inr, ⟨coprodIsCoprod A.cover B.cover⟩,
      hP.symm⟩

/-- The initial-apex statement from the S1833 affine initial object and its
universal property. -/
theorem S1899InitialApex_of_affine (e : S1833AffineEquiv)
    (h : S1866CoproductApexFirstMissingAffine e) : S1899InitialApex := by
  obtain ⟨P, hP⟩ := S1899CoherentCoverOfStrong
    ((S1866StrongCoverOf_iff_baseChange (S1833InitialObj e)).mpr h.1)
  exact ⟨P, ⟨hP.symm ▸ S1833InitialObj_isInitial e⟩⟩

/-- The binary coproduct target from the S1833 affine coproduct object and its
universal property (`S1866CoproductApexFirstMissingAffine`). -/
theorem S1899BinaryCoproductApex_of_affine (e : S1833AffineEquiv)
    (h : S1866CoproductApexFirstMissingAffine e) : S1899BinaryCoproductApex := by
  intro A B
  obtain ⟨P, hP⟩ := S1899CoherentCoverOfStrong
    ((S1866StrongCoverOf_iff_baseChange (S1833CoproductObj e A.cover B.cover)).mpr
      (h.2 A B))
  exact ⟨P, S1833CoproductCofan e A.cover B.cover,
    ⟨S1833CoproductCofan_isColimit e A.cover B.cover⟩, hP.symm⟩

/-- **The affine bridge's coproduct condition (S1866's affine first missing)
implies the choice-free coproduct target.** -/
theorem S1899CoproductApex_of_affine (e : S1833AffineEquiv)
    (h : S1866CoproductApexFirstMissingAffine e) : S1899CoproductApex :=
  ⟨S1899InitialApex_of_affine e h, S1899BinaryCoproductApex_of_affine e h⟩

/-- The affine coproduct condition gives finite coproducts on the coherent
category, without any chosen-`Limits.coproduct` coherence condition. -/
theorem S1899HasFiniteCoproducts_of_affine (e : S1833AffineEquiv)
    (h : S1866CoproductApexFirstMissingAffine e) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 :=
  S1899HasFiniteCoproducts (S1899CoproductApex_of_affine e h)

/-! ## 7. Non-vacuity: cospans with an identity leg -/

/-- The identity-leg two-pullback datum with the explicit apex, used only to make
the apex known on the nose.  Its fields are S1832's identity-leg construction. -/
noncomputable def S1899IdRightTwoPullback {A C : CoherentCover}
    (f : S1728CoverMap A.cover C.cover) :
    S1832TwoPullback f (S1641CoverMapId C.cover) where
  apex := A.cover
  toA := S1641CoverMapId A.cover
  toB := f
  commutes := (S1728LeftUnitorIso f).trans (S1728RightUnitorIso f).symm
  lift := fun _ c => c.toA
  liftToA := fun _ c => S1728RightUnitorIso c.toA
  liftToB := fun _ c => c.commutes.trans (S1728RightUnitorIso c.toB)
  uniq := fun _ _ _ h1 _ => by
    obtain ⟨e⟩ := h1
    exact ⟨(S1728RightUnitorIso _).symm.trans e⟩

/-- The other identity-leg datum. -/
noncomputable def S1899IdLeftTwoPullback {B C : CoherentCover}
    (g : S1728CoverMap B.cover C.cover) :
    S1832TwoPullback (S1641CoverMapId C.cover) g where
  apex := B.cover
  toA := g
  toB := S1641CoverMapId B.cover
  commutes := (S1728RightUnitorIso g).trans (S1728LeftUnitorIso g).symm
  lift := fun _ c => c.toB
  liftToA := fun _ c => c.commutes.symm.trans (S1728RightUnitorIso c.toA)
  liftToB := fun _ c => S1728RightUnitorIso c.toB
  uniq := fun _ _ _ _ h2 => by
    obtain ⟨e⟩ := h2
    exact ⟨(S1728RightUnitorIso _).symm.trans e⟩

/-- **Identity-leg cospans satisfy the target**, with the apex the other coherent
cover.  Hence the target is satisfiable and not vacuous. -/
theorem S1899IdentityLegPullbackApex {A C : CoherentCover}
    (f : S1728CoverMap A.cover C.cover) :
    S1899TwoPullbackApexStrong f (S1641CoverMapId C.cover) :=
  ⟨S1899IdRightTwoPullback f,
    (S1866StrongCoverOf_iff_coherent A.cover).mpr ⟨A, rfl⟩⟩

/-- The other identity-leg case. -/
theorem S1899IdentityLegPullbackApex_left {B C : CoherentCover}
    (g : S1728CoverMap B.cover C.cover) :
    S1899TwoPullbackApexStrong (S1641CoverMapId C.cover) g :=
  ⟨S1899IdLeftTwoPullback g,
    (S1866StrongCoverOf_iff_coherent B.cover).mpr ⟨B, rfl⟩⟩

/-! ## 8. The choice of presentation is load-bearing -/

/-- The identity cover map of the terminal cover, as an actual cover map of the
S1726 orbicurve cover category. -/
abbrev S1899IdentityCoverMap : S1728CoverMap S1762TerminalCover S1762TerminalCover :=
  S1866IdentityCoverMap

/-- **The identity cospan of the terminal cover has two two-pullback data with
non-equivalent apexes**: one is the coherent terminal cover, the other is S1850's
doubled cover, which is isomorphic to it as a cover and has the same source and
structure map but carries no strong structure.  The strong presentation of the
apex is therefore an input that must be produced (or chosen), not a consequence
of the two-pullback universal property. -/
theorem S1899ApexPresentationLoadBearing :
    (∃ P : S1832TwoPullback S1899IdentityCoverMap S1899IdentityCoverMap,
        S1866StrongCoverOf P.apex) ∧
      (∃ Q : S1832TwoPullback S1899IdentityCoverMap S1899IdentityCoverMap,
        ¬ S1866StrongCoverOf Q.apex) :=
  ⟨⟨S1866TerminalApexTwoPullback, S1866StrongCoverOf_terminal⟩,
    ⟨S1866DoubledApexTwoPullback,
      fun h => S1866StrongCoverOf_doubled_not h⟩⟩

/-- **It is not the case that every two-pullback apex is strong**, restated at the
S1899 target: the target must select the *presented* apex, and in particular it
cannot be discharged by an arbitrary witness of the universal property. -/
theorem S1899NotEveryTwoPullbackApexStrong :
    ¬ (∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
        (P : S1832TwoPullback f g), S1866StrongCoverOf P.apex) :=
  S1866TwoPullbackApexAllStrong_false

/-- Coherence is not invariant under isomorphism of recorded covers: the
terminal cover is coherent, the doubled cover is not, and they are isomorphic.
Hence a construction that produces the pullback apex only up to isomorphism
cannot establish the target; the strong structure must be produced on the nose. -/
theorem S1899Coherence_not_isoInvariant :
    (∃ C : CoherentCover, C.cover = S1762TerminalCover) ∧
      (¬ ∃ C : CoherentCover, C.cover = S1850DoubledCover) ∧
      Nonempty (S1762TerminalCover ≅ S1850DoubledCover) :=
  S1866Coherence_not_iso_invariant

/-! ## 9. The exact first missing, in the form of named statements -/

/-- **The first geometric missing**: the pointwise two-fibre product of the
covers' source stacks is a stack.  This is S1891's named descent theorem, which
Mathlib does not contain (no closure of `Pseudofunctor.IsStack` under pointwise
two-fibre products). -/
def S1899DescentFirstMissing : Prop := S1891StackTwoFiberProductDescent.{0}

/-- **The constructive limit-cone form of the target.**  For every cospan of
actual cover maps between coherent covers, the cospan of their classes in the
S1728 category has an actual limit cone whose point is the underlying cover of a
coherent cover.  This is the "coherent apex of the pullback" statement with the
limit cone exhibited, and it is a consequence of the choice-free target. -/
def S1899CoherentPullbackApex : Prop :=
  ∀ (A B C : CoherentCover) (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover),
    ∃ (P : CoherentCover) (c : PullbackCone (S1832Q f) (S1832Q g)),
      Nonempty (IsLimit c) ∧ c.pt = P.cover

/-- The choice-free target exhibits the coherent limit cone. -/
theorem S1899CoherentPullbackApex_of_twoPullback (h : S1899TwoPullbackApexStrongAll) :
    S1899CoherentPullbackApex := by
  intro A B C f g
  obtain ⟨P, hP⟩ := h A B C f g
  obtain ⟨Q, hQ⟩ := S1899CoherentCoverOfStrong hP
  exact ⟨Q, S1832PullbackCone P, ⟨S1832PullbackConeIsLimit P⟩, hQ.symm⟩

/-- The geometric construction also exhibits the coherent limit cone. -/
theorem S1899CoherentPullbackApex_of_geometric (h : S1899GeometricStrongIsoCommaAll) :
    S1899CoherentPullbackApex :=
  S1899CoherentPullbackApex_of_twoPullback (S1899TwoPullbackApexStrongAll_of_geometric h)

/-- S1866's chosen-apex condition also exhibits the coherent limit cone. -/
theorem S1899CoherentPullbackApex_of_chosen (h : HasPullbacks S1728Cover)
    (hA : S1866PullbackApexFirstMissing h) : S1899CoherentPullbackApex :=
  S1899CoherentPullbackApex_of_twoPullback (S1899TwoPullbackApexStrongAll_of_chosen h hA)

/-- **The limit-cone form also gives pullbacks on the coherent covers.**  The
exhibited limit cone (whose point is the underlying cover of a coherent cover) is
used directly by the creation argument; the classical choice of the S1728
pullback is never consulted. -/
theorem S1899HasPullbacks_of_coherentLimitCone (h : S1899CoherentPullbackApex) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 := by
  haveI : ∀ {X Y Z : S1856StrictSub} {f : X ⟶ Z} {g : Y ⟶ Z},
      HasLimit (cospan f g) := by
    intro X Y Z f g
    rcases X with ⟨X0, ⟨A, hAX⟩⟩
    rcases Y with ⟨Y0, ⟨B, hBY⟩⟩
    rcases Z with ⟨Z0, ⟨C, hCZ⟩⟩
    subst hAX
    subst hBY
    subst hCZ
    obtain ⟨P, c, ⟨hc⟩, hpt⟩ := h A B C (Quot.out f.hom) (Quot.out g.hom)
    have hdiag : cospan (S1832Q (Quot.out f.hom)) (S1832Q (Quot.out g.hom)) =
        cospan f.hom g.hom := by
      rw [S1832Q_out f.hom, S1832Q_out g.hom]
    let c' : PullbackCone f.hom g.hom :=
      (Cone.postcompose (eqToIso hdiag.symm).inv).obj c
    have hc' : IsLimit c' := (IsLimit.postcomposeInvEquiv (eqToIso hdiag.symm) c).symm hc
    let alpha := cospanCompIso S1856StrictProperty.ι f g
    let c0 : Cone ((cospan f g) ⋙ S1856StrictProperty.ι) := (Cone.postcompose alpha.inv).obj c'
    have hc0 : IsLimit c0 := (IsLimit.postcomposeInvEquiv alpha c').symm hc'
    have hQ : S1856StrictProperty c0.pt := by
      show S1856StrictProperty c.pt
      rw [hpt]
      exact ⟨P, rfl⟩
    haveI hKl : HasLimit ((cospan f g) ⋙ S1856StrictProperty.ι) := HasLimit.mk ⟨c0, hc0⟩
    letI : CreatesLimit (cospan f g) S1856StrictProperty.ι :=
      createsLimitFullSubcategoryInclusion' (cospan f g) hc0 hQ
    exact hasLimit_of_created (cospan f g) S1856StrictProperty.ι
  exact @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    S1856StrictSub _ CoherentCover _ WalkingCospan _
    S1856ToStrict S1856ToStrict_isEquivalence
    (@hasPullbacks_of_hasLimit_cospan S1856StrictSub _ this)

/-- The exact first missing, in one statement: `S1899GeometricStrongIsoCommaAll`.
Its consequences are the choice-free target and hence the categorical limits on
the coherent covers; its insufficiency (weakly) is S1866's no-go above, and its
unavailable components are S1864's pseudofunctor/descent/structure-map obligation
and the strong structure on the apex's recorded presentations.  The limit-cone
form `S1899CoherentPullbackApex`, its derivation from the target and its own
consumer are recorded in the same section. -/
theorem S1899FirstMissing_consumers (h : S1899GeometricStrongIsoCommaAll) :
    S1899PullbackApexPresentationsStrong ∧
      (@HasPullbacks CoherentCover S1854CoherentCategory11) :=
  ⟨S1899Presentations_of_geometric h, S1899HasPullbacks_of_geometric h⟩

/-- **The exact first missing for finite coproducts**: the choice-free coherent
coproduct apex `S1899CoproductApex`.  The existing tree supplies it from the
affine bridge (S1866's affine condition, hence from S1833's affine equivalence
plus apex strongness), but the geometric initial/coproduct covers with strong
structure are not constructed; Mathlib has no closure of `IsStack` under
pointwise coproducts (see S1833). -/
def S1899CoproductFirstMissing : Prop := S1899CoproductApex

/-- The coproduct first missing gives finite coproducts on the coherent
category. -/
theorem S1899FiniteCoproducts_of_firstMissing (h : S1899CoproductFirstMissing) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 :=
  S1899HasFiniteCoproducts h

/-! ## 10. Checks -/

#check S1899TwoPullbackApexStrong
#check S1899PullbackApexPresentationsStrong
#check S1899TwoPullbackApexStrongAll
#check S1899Presentations_iff_twoPullbackApex
#check S1899CoherentCoverOfStrong
#check S1899HasPullbacksStrictSub
#check S1899HasPullbacks_of_twoPullbackApex
#check S1899HasPullbacks_of_presentations
#check S1899AffineTargetHasPullbacks
#check S1899HasPullbacks_of_essSurj
#check S1899HasPullbacks_of_bridge
#check S1899GeometricStrongIsoComma
#check S1899GeometricStrongIsoCommaAll
#check S1899IsoCommaObligationAll
#check S1899TwoPullbackApexStrongAll_of_geometric
#check S1899Presentations_of_geometric
#check S1899HasPullbacks_of_geometric
#check S1899IsoCommaObligationAll_of_geometric
#check S1899Presentations_of_chosen
#check S1899TwoPullbackApexStrongAll_of_chosen
#check S1899InitialApex
#check S1899BinaryCoproductApex
#check S1899CoproductApex
#check S1899HasInitialStrictSub
#check S1899HasBinaryCoproductsStrictSub
#check S1899HasInitial
#check S1899HasBinaryCoproducts
#check S1899HasFiniteCoproducts
#check S1899CoproductApex_of_chosen
#check S1899InitialApex_of_affine
#check S1899BinaryCoproductApex_of_affine
#check S1899CoproductApex_of_affine
#check S1899HasFiniteCoproducts_of_affine
#check S1899IdRightTwoPullback
#check S1899IdLeftTwoPullback
#check S1899IdentityLegPullbackApex
#check S1899IdentityLegPullbackApex_left
#check S1899ApexPresentationLoadBearing
#check S1899NotEveryTwoPullbackApexStrong
#check S1899Coherence_not_isoInvariant
#check S1899DescentFirstMissing
#check S1899CoherentPullbackApex
#check S1899CoherentPullbackApex_of_twoPullback
#check S1899CoherentPullbackApex_of_geometric
#check S1899CoherentPullbackApex_of_chosen
#check S1899HasPullbacks_of_coherentLimitCone
#check S1899FirstMissing_consumers
#check S1899CoproductFirstMissing
#check S1899FiniteCoproducts_of_firstMissing

#print axioms S1899Presentations_iff_twoPullbackApex
#print axioms S1899CoherentCoverOfStrong
#print axioms S1899HasPullbacksStrictSub
#print axioms S1899HasPullbacks_of_twoPullbackApex
#print axioms S1899HasPullbacks_of_presentations
#print axioms S1899AffineTargetHasPullbacks
#print axioms S1899HasPullbacks_of_essSurj
#print axioms S1899HasPullbacks_of_bridge
#print axioms S1899TwoPullbackApexStrongAll_of_geometric
#print axioms S1899Presentations_of_geometric
#print axioms S1899HasPullbacks_of_geometric
#print axioms S1899IsoCommaObligationAll_of_geometric
#print axioms S1899Presentations_of_chosen
#print axioms S1899TwoPullbackApexStrongAll_of_chosen
#print axioms S1899HasInitialStrictSub
#print axioms S1899HasBinaryCoproductsStrictSub
#print axioms S1899HasInitial
#print axioms S1899HasBinaryCoproducts
#print axioms S1899HasFiniteCoproducts
#print axioms S1899CoproductApex_of_chosen
#print axioms S1899InitialApex_of_affine
#print axioms S1899BinaryCoproductApex_of_affine
#print axioms S1899CoproductApex_of_affine
#print axioms S1899HasFiniteCoproducts_of_affine
#print axioms S1899IdRightTwoPullback
#print axioms S1899IdLeftTwoPullback
#print axioms S1899IdentityLegPullbackApex
#print axioms S1899IdentityLegPullbackApex_left
#print axioms S1899ApexPresentationLoadBearing
#print axioms S1899NotEveryTwoPullbackApexStrong
#print axioms S1899Coherence_not_isoInvariant
#print axioms S1899CoherentPullbackApex_of_twoPullback
#print axioms S1899CoherentPullbackApex_of_geometric
#print axioms S1899CoherentPullbackApex_of_chosen
#print axioms S1899HasPullbacks_of_coherentLimitCone
#print axioms S1899FirstMissing_consumers
#print axioms S1899FiniteCoproducts_of_firstMissing

end LeanFormal.IUT.XiFPaper.S1899CoherentStrongApexActual