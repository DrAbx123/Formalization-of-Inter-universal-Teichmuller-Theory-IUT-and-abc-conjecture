/-
# S1856: the coherent category has pullbacks and finite coproducts
  once the S1728 limit apexes are coherent

## The question

S1854 constructed the actual category

  S1854CoherentCategory11 : Category.{1,1} CoherentCover

and the forgetful functor

  S1854Forget11 : CoherentCover ⥤ S1728Cover,

proved it full and faithful, and transported the terminal object and S1828 R1.
It left the pullback and finite-coproduct structures open, naming the exact
remaining geometric input as

  S1854PullbackApexCoherent h        (the S1728 pullback apex of a cospan of
                                      coherent covers is the underlying cover of
                                      a coherent cover),
  S1854CoproductApexCoherent h0 h2   (the same for the initial object and the
                                      binary coproducts),

and recording the transports themselves as the unproved propositions
S1854PullbackTransport and S1854CoproductTransport:

  HasPullbacks S1728Cover + apex coherence  ->  HasPullbacks CoherentCover,
  HasInitial/BinaryCoproducts S1728Cover + apex coherence
    -> HasInitial/BinaryCoproducts CoherentCover.

## What is proved here

1. The transports are proved, not assumed.  The proof is the standard
   "a full-and-faithful functor reflects limits/colimits once the apex is in
   the image", implemented through Mathlib's full-subcategory creation:

   * S1856StrictProperty is the property "Y is literally A.cover for some
     coherent A"; S1856StrictSub is its full subcategory of S1728Cover.
   * For a cospan in S1856StrictSub, the S1728 pullback cone of the underlying
     maps is a limit; apex coherence makes its apex (P.cover) an object of the
     strict subcategory; createsLimitFullSubcategoryInclusion' then creates the
     pullback in the full subcategory.  HasPullback.of_createsLimit packages it.
   * The same for the initial object and binary coproducts, using
     createsColimitFullSubcategoryInclusion' and coproduct apex coherence.
   * S1856ToStrict : CoherentCover ⥤ S1856StrictSub is the restriction of the
     forgetful functor; it is full, faithful and essentially surjective (indeed
     bijective on objects), hence an equivalence.  Transporting HasPullbacks /
     HasInitial / HasBinaryCoproducts across this equivalence via
     Adjunction.hasLimitsOfShape_of_equivalence /
     hasColimitsOfShape_of_equivalence gives the statements for CoherentCover.

   No cone is fabricated: the limits in the strict subcategory are created from
   the actual S1728 limit cones, and the equivalence transport is the usual
   one.  In particular the transported HasPullbacks is the actual Mathlib
   HasPullbacks at S1854CoherentCategory11.

2. Conditional results:

     S1856HasPullbacks (h) (hA) : HasPullbacks CoherentCover,
     S1856HasInitial (h0) (h2) (hA) : HasInitial CoherentCover,
     S1856HasBinaryCoproducts ... : HasBinaryCoproducts CoherentCover,
     S1856HasFiniteCoproducts ... : HasFiniteCoproducts CoherentCover.

   Consequently S1854PullbackTransport and S1854CoproductTransport are
   theorems.

3. The exact remaining input (the corrected first missing).  The old S1854
   statements

     S1854PullbackFirstMissing = S1832FirstMissingPullback ∧ S1854PullbackTransport,
     S1854CoproductFirstMissing = S1833FirstMissing ∧ S1854CoproductTransport

   with the transports now proved, reduce to S1832FirstMissingPullback and
   S1833FirstMissing.  But those alone do *not* give the coherent structures:
   the transport is conditional on apex coherence.  The precise first missing
   for the coherent category is therefore

     S1856PullbackFirstMissing :=
       ∃ h : S1832FirstMissingPullback,
         S1854PullbackApexCoherent (S1832HasPullbacks_of_squares h),

     S1856CoproductFirstMissing :=
       S1833FirstMissing ∧
         ∃ h0 : HasInitial S1728Cover, ∃ h2 : HasBinaryCoproducts S1728Cover,
           S1854CoproductApexCoherent h0 h2.

   These are exactly the inputs consumed by S1856HasPullbacks /
   S1856HasFiniteCoproducts; the implications are proved.

## Honest boundary

* S1832FirstMissingPullback and S1833FirstMissing are not proved here (they are
  the geometric inputs of S1832/S1833); apex coherence is not proved either.
  What is proved is that these are *exactly* what is missing: the transports
  are theorems, not assumptions.
* No fake limit, no additional axiom, no change to any existing definition.
* Only propext, Classical.choice and Quot.sound occur; see the audit block.
-/

import tmp.sheaf.xif.paper.S1854CoherentCategoryActual
import tmp.sheaf.xif.paper.S1832ActualCoverPullbacksActual
import tmp.sheaf.xif.paper.S1833ActualCoverCoproductsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual

open CategoryTheory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut

universe u v w x

open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
open LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual
open LeanFormal.IUT.XiFPaper.S1828SliceR1Actual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual

attribute [local instance] S1854CoherentCategory11

/-! ## 1. The strict image subcategory of the S1728 cover category -/

/-- The strict image of the forgetful functor: Y is *literally* the underlying
cover of a coherent cover.  This is stronger than the essential image (which
uses isomorphism); it is the property for which the apex coherence hypotheses
S1854PullbackApexCoherent and S1854CoproductApexCoherent give the apex
*on the nose*. -/
def S1856StrictProperty : ObjectProperty S1728Cover :=
  fun Y => ∃ A : CoherentCover, A.cover = Y

/-- The full subcategory of S1728Cover on the strict image of the coherent
covers. -/
abbrev S1856StrictSub : Type 1 := S1856StrictProperty.FullSubcategory

/-- The forgetful functor, restricted to the strict image.  It is the identity on
the underlying covers and on the hom maps. -/
noncomputable def S1856ToStrict : CoherentCover ⥤ S1856StrictSub where
  obj A := ⟨A.cover, ⟨A, rfl⟩⟩
  map {A B} f := ObjectProperty.homMk (S1854Forget11.map f)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact S1854Forget11.map_id A
  map_comp {A B C} f g := by
    apply ObjectProperty.hom_ext
    exact S1854Forget11.map_comp f g

/-- The restricted forgetful functor is full. -/
noncomputable instance S1856ToStrict_full : S1856ToStrict.Full where
  map_surjective {A B} f := by
    obtain ⟨g, hg⟩ := S1854Forget11_full.map_surjective f.hom
    exact ⟨g, by apply ObjectProperty.hom_ext; exact hg⟩

/-- The restricted forgetful functor is faithful. -/
noncomputable instance S1856ToStrict_faithful : S1856ToStrict.Faithful where
  map_injective {A B} f g h := by
    apply S1854Forget11_faithful.map_injective
    exact congrArg (fun k => k.hom) h

/-- The restricted forgetful functor is essentially surjective: every object of
the strict image is of the form A.cover for some coherent A, and the property
proofs are irrelevant. -/
noncomputable instance S1856ToStrict_essSurj : S1856ToStrict.EssSurj where
  mem_essImage X := by
    rcases X.property with ⟨A, hA⟩
    exact ⟨A, ⟨ObjectProperty.isoMk S1856StrictProperty
      (X := S1856ToStrict.obj A) (Y := X) (eqToIso hA)⟩⟩

/-- The restricted forgetful functor is an equivalence. -/
noncomputable instance S1856ToStrict_isEquivalence : S1856ToStrict.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-! ## 2. Pullbacks on the strict image -/

/-- **Pullbacks on the strict image.**  A cospan in S1856StrictSub has an
underlying cospan in S1728Cover; its S1728 pullback cone is a limit.  Apex
coherence supplies a coherent P0 whose underlying cover is the pullback apex,
so this cone lives over an object of the strict image, and
createsLimitFullSubcategoryInclusion' creates the pullback in the full
subcategory.  No cone is fabricated: the cone is the actual S1728 pullback cone
transported along the canonical cospan comparison. -/
theorem S1856HasPullbacksStrictSub (h : Limits.HasPullbacks S1728Cover)
    (hA : S1854PullbackApexCoherent h) : Limits.HasPullbacks S1856StrictSub := by
  letI := h
  haveI : ∀ {X Y Z : S1856StrictSub} {f : X ⟶ Z} {g : Y ⟶ Z},
      HasLimit (cospan f g) := by
    intro X Y Z f g
    rcases X with ⟨X0, ⟨A, hAX⟩⟩
    rcases Y with ⟨Y0, ⟨B, hBY⟩⟩
    rcases Z with ⟨Z0, ⟨C, hCZ⟩⟩
    subst hAX
    subst hBY
    subst hCZ
    obtain ⟨P0, hP0⟩ := hA A B C f.hom g.hom
    let alpha := cospanCompIso S1856StrictProperty.ι f g
    let c0 : Cone ((cospan f g) ⋙ S1856StrictProperty.ι) :=
      (Cone.postcompose alpha.inv).obj (pullback.cone f.hom g.hom)
    have hc0 : IsLimit c0 :=
      (IsLimit.postcomposeInvEquiv alpha (pullback.cone f.hom g.hom)).symm
        (pullback.isLimit f.hom g.hom)
    let e : P0.cover ⟶ c0.pt := eqToHom hP0
    haveI : IsIso e := by infer_instance
    let cExt : Cone ((cospan f g) ⋙ S1856StrictProperty.ι) := c0.extend e
    have hcExt : IsLimit cExt := IsLimit.extendIso e hc0
    have hQ : S1856StrictProperty cExt.pt := ⟨P0, rfl⟩
    letI : CreatesLimit (cospan f g) S1856StrictProperty.ι :=
      createsLimitFullSubcategoryInclusion' (cospan f g) hcExt hQ
    exact HasPullback.of_createsLimit S1856StrictProperty.ι f g
  exact @hasPullbacks_of_hasLimit_cospan S1856StrictSub _ this

/-! ## 3. Initial objects and binary coproducts on the strict image -/

/-- **The initial object on the strict image.**  Apex coherence gives a coherent
P0 whose underlying cover is the S1728 initial object; the latter is initial in
S1728Cover, and the strict subcategory has the same homs, so it is initial
there too. -/
theorem S1856HasInitialStrictSub (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) : Limits.HasInitial S1856StrictSub := by
  letI := h0
  letI := h2
  obtain ⟨P0, hP0⟩ := hA.1
  let Q : S1856StrictSub := ⟨⊥_ S1728Cover, ⟨P0, hP0⟩⟩
  have hQ : IsInitial Q := by
    refine IsInitial.ofUniqueHom (fun Y => ObjectProperty.homMk (initial.to Y.obj)) ?_
    intro Y m
    apply ObjectProperty.hom_ext
    exact initial.hom_ext m.hom (initial.to Y.obj)
  exact IsInitial.hasInitial hQ

/-- **Binary coproducts on the strict image.**  For X Y in the strict image,
choose coherent preimages P Q; apex coherence gives a coherent R whose
underlying cover is P.cover ⨿ Q.cover.  The S1728 coproduct cofan is a
colimit; transporting it along the pair comparison and extending the apex to
R.cover gives a cocone over the diagram of X Y whose apex is in the strict
image, so createsColimitFullSubcategoryInclusion' creates the coproduct. -/
theorem S1856HasBinaryCoproductsStrictSub (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    Limits.HasBinaryCoproducts S1856StrictSub := by
  letI := h0
  letI := h2
  haveI : ∀ {X Y : S1856StrictSub}, HasColimit (pair X Y) := by
    intro X Y
    obtain ⟨P, hPX⟩ := X.property
    obtain ⟨Q, hQY⟩ := Y.property
    obtain ⟨R, hR⟩ := hA.2 P Q
    let beta : pair P.cover Q.cover ≅ pair X.obj Y.obj :=
      mapPairIso (eqToIso hPX) (eqToIso hQY)
    let d0 : BinaryCofan P.cover Q.cover := BinaryCofan.mk coprod.inl coprod.inr
    let d1 : BinaryCofan X.obj Y.obj := (Cocone.precompose beta.symm.hom).obj d0
    have hd1 : IsColimit d1 :=
      (IsColimit.precomposeHomEquiv beta.symm d0).symm (coprodIsCoprod P.cover Q.cover)
    let alpha := pairComp X Y S1856StrictProperty.ι
    let c0 : Cocone ((pair X Y) ⋙ S1856StrictProperty.ι) :=
      (Cocone.precompose alpha.hom).obj d1
    have hc0 : IsColimit c0 :=
      (IsColimit.precomposeHomEquiv alpha d1).symm hd1
    let e : c0.pt ⟶ R.cover := eqToHom hR.symm
    haveI : IsIso e := by infer_instance
    let cExt : Cocone ((pair X Y) ⋙ S1856StrictProperty.ι) := c0.extend e
    have hcExt : IsColimit cExt := IsColimit.extendIso e hc0
    have hRprop : S1856StrictProperty cExt.pt := ⟨R, rfl⟩
    letI : CreatesColimit (pair X Y) S1856StrictProperty.ι :=
      createsColimitFullSubcategoryInclusion' (pair X Y) hcExt hRprop
    haveI : HasColimit ((pair X Y) ⋙ S1856StrictProperty.ι) :=
      hasColimit_of_iso (pairComp X Y S1856StrictProperty.ι)
    exact hasColimit_of_created (pair X Y) S1856StrictProperty.ι
  exact @hasBinaryCoproducts_of_hasColimit_pair S1856StrictSub _ this

/-! ## 4. Transport to the coherent category -/

/-- **The coherent category has pullbacks**, given the S1728 pullbacks and apex
coherence.  This is HasPullbacks transported across the equivalence
S1856ToStrict. -/
theorem S1856HasPullbacks (h : Limits.HasPullbacks S1728Cover)
    (hA : S1854PullbackApexCoherent h) :
    @Limits.HasPullbacks CoherentCover S1854CoherentCategory11 :=
  @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    S1856StrictSub _ CoherentCover _ WalkingCospan _ S1856ToStrict
    S1856ToStrict_isEquivalence (S1856HasPullbacksStrictSub h hA)

/-- **The coherent category has an initial object**, given the S1728 initial
object and binary coproducts and coproduct apex coherence. -/
theorem S1856HasInitial (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasInitial CoherentCover S1854CoherentCategory11 :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 S1856StrictSub _ (Discrete PEmpty) _
    S1856ToStrict S1856ToStrict_isEquivalence (S1856HasInitialStrictSub h0 h2 hA)

/-- **The coherent category has binary coproducts**, given the S1728 initial
object and binary coproducts and coproduct apex coherence. -/
theorem S1856HasBinaryCoproducts (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasBinaryCoproducts CoherentCover S1854CoherentCategory11 :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 S1856StrictSub _ (Discrete WalkingPair) _
    S1856ToStrict S1856ToStrict_isEquivalence
    (S1856HasBinaryCoproductsStrictSub h0 h2 hA)

/-- **The coherent category has finite coproducts**, given the S1728 initial
object and binary coproducts and coproduct apex coherence. -/
theorem S1856HasFiniteCoproducts (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory11 := by
  letI : Limits.HasInitial CoherentCover := S1856HasInitial h0 h2 hA
  letI : Limits.HasBinaryCoproducts CoherentCover := S1856HasBinaryCoproducts h0 h2 hA
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-! ## 5. The S1854 transports are theorems -/

/-- **S1854PullbackTransport is proved.**  The full-and-faithful forgetful
functor reflects the actual S1728 pullback cones once the apex is the
underlying cover of a coherent cover. -/
theorem S1856PullbackTransport : S1854PullbackTransport := by
  intro h hA
  exact S1856HasPullbacks h hA

/-- **S1854CoproductTransport is proved.**  The same reflection argument for the
initial object and binary coproducts. -/
theorem S1856CoproductTransport : S1854CoproductTransport := by
  intro h0 h2 hA
  exact ⟨S1856HasInitial h0 h2 hA, S1856HasBinaryCoproducts h0 h2 hA⟩

/-! ## 6. The precise first missing -/

/-- **The exact first missing for pullbacks on the coherent covers**: S1832's
bicategorical fibre-product input together with apex coherence for the pullback
structure it induces.  This is precisely the input of S1856HasPullbacks. -/
def S1856PullbackFirstMissing : Prop :=
  ∃ h : S1832FirstMissingPullback,
    S1854PullbackApexCoherent (S1832HasPullbacks_of_squares h)

/-- **The exact first missing for finite coproducts on the coherent covers**:
S1833's affine/slice comparison together with coproduct apex coherence for a
chosen S1728 initial object and binary-coproduct structure. -/
def S1856CoproductFirstMissing : Prop :=
  S1833FirstMissing ∧
    ∃ h0 : Limits.HasInitial S1728Cover,
    ∃ h2 : Limits.HasBinaryCoproducts S1728Cover,
      S1854CoproductApexCoherent h0 h2

/-- **The pullback first missing suffices for HasPullbacks on the coherent
category.** -/
theorem S1856HasPullbacks_of_firstMissing :
    S1856PullbackFirstMissing →
      @Limits.HasPullbacks CoherentCover S1854CoherentCategory11 := by
  rintro ⟨h, hA⟩
  exact S1856HasPullbacks (S1832HasPullbacks_of_squares h) hA

/-- **The coproduct first missing suffices for finite coproducts on the
coherent category.** -/
theorem S1856HasFiniteCoproducts_of_firstMissing :
    S1856CoproductFirstMissing →
      @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory11 := by
  rintro ⟨_, h0, h2, hA⟩
  exact S1856HasFiniteCoproducts h0 h2 hA

/-- A direct form of the pullback first missing, from S1832's statement and
apex coherence for the pullback structure it induces. -/
theorem S1856PullbackFirstMissing_of_S1832
    (h : S1832FirstMissingPullback)
    (hA : S1854PullbackApexCoherent (S1832HasPullbacks_of_squares h)) :
    S1856PullbackFirstMissing :=
  ⟨h, hA⟩

/-- A direct form of the coproduct first missing, from S1833's statement and
coproduct apex coherence for a chosen S1728 initial object and binary-coproduct
structure. -/
theorem S1856CoproductFirstMissing_of_S1833
    (h : S1833FirstMissing)
    (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    S1856CoproductFirstMissing :=
  ⟨h, h0, h2, hA⟩

/-- **The old S1854 pullback first-missing proposition is now equivalent to
S1832's input.**  This only records the S1728 side plus the (now proved,
conditional) transport; it does *not* assert apex coherence, and hence it is
strictly weaker than S1856PullbackFirstMissing.  The latter is the correct
first missing for HasPullbacks CoherentCover. -/
theorem S1854PullbackFirstMissing_iff :
    S1854PullbackFirstMissing ↔ S1832FirstMissingPullback :=
  ⟨fun h => h.1, fun h => ⟨h, S1856PullbackTransport⟩⟩

/-- **The old S1854 coproduct first-missing proposition is now equivalent to
S1833's input.**  As for pullbacks, this is weaker than
S1856CoproductFirstMissing, which additionally requires apex coherence. -/
theorem S1854CoproductFirstMissing_iff :
    S1854CoproductFirstMissing ↔ S1833FirstMissing :=
  ⟨fun h => h.1, fun h => ⟨h, S1856CoproductTransport⟩⟩

/-! ## 7. Checks and axiom audit -/

#check S1856StrictProperty
#check S1856StrictSub
#check S1856ToStrict
#check S1856ToStrict_full
#check S1856ToStrict_faithful
#check S1856ToStrict_essSurj
#check S1856ToStrict_isEquivalence
#check S1856HasPullbacksStrictSub
#check S1856HasInitialStrictSub
#check S1856HasBinaryCoproductsStrictSub
#check S1856HasPullbacks
#check S1856HasInitial
#check S1856HasBinaryCoproducts
#check S1856HasFiniteCoproducts
#check S1856PullbackTransport
#check S1856CoproductTransport
#check S1856PullbackFirstMissing
#check S1856CoproductFirstMissing
#check S1856HasPullbacks_of_firstMissing
#check S1856HasFiniteCoproducts_of_firstMissing
#check S1856PullbackFirstMissing_of_S1832
#check S1856CoproductFirstMissing_of_S1833
#check S1854PullbackFirstMissing_iff
#check S1854CoproductFirstMissing_iff

#print axioms S1856ToStrict
#print axioms S1856ToStrict_isEquivalence
#print axioms S1856HasPullbacksStrictSub
#print axioms S1856HasInitialStrictSub
#print axioms S1856HasBinaryCoproductsStrictSub
#print axioms S1856HasPullbacks
#print axioms S1856HasInitial
#print axioms S1856HasBinaryCoproducts
#print axioms S1856HasFiniteCoproducts
#print axioms S1856PullbackTransport
#print axioms S1856CoproductTransport
#print axioms S1856HasPullbacks_of_firstMissing
#print axioms S1856HasFiniteCoproducts_of_firstMissing
#print axioms S1854PullbackFirstMissing_iff
#print axioms S1854CoproductFirstMissing_iff

end LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
