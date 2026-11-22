/-
# S1867: finite-group quotients and the mono/direct-summand field on the
  coherent covers

## Result

* The finite-group quotient field is transported to the coherent categories
  S1854CoherentCategory11 and S1854CoherentCategory01.  It is conditional on
  S1792's cover-slice comparison and on the coherence of the actual quotient
  apexes.  The quotient objects and cocones are S1792's, with S1815 supplying
  the affine quotient colimits.  The transport goes through the strict image
  S1856StrictSub, the equivalence S1856ToStrict, and the target-universe
  equivalence S1857Coherent01To11.  The exact first missing for the quotient
  field is therefore the pair (S1792 cover-slice equivalence, quotient apex
  coherence); it is recorded as S1867QuotientFirstMissing11 and
  S1867QuotientFirstMissing01.

* The mono/direct-summand field is NOT transported.  The exact geometric first
  missing is recorded: S1791's component factorization for the underlying
  ambient map of each coherent mono, together with the coherence of the
  ambient complement apexes.  The remaining categorical lift of the S1791
  ambient colimit through the full-subcategory inclusion is recorded as
  S1867MonoTransport with no inhabitant asserted.  An alternative
  equivalence route needs the essential-image gap S1867CoherentEssImage and is
  recorded as S1867MonoTransportEss.  Neither transport proposition is proved
  or assumed.

## Honest boundary

No sorry, no admit, no new axiom, no fake quotient, no fake complement.  All
missing inputs are plain Prop definitions with no inhabitant; only the
quotient transport is asserted as a theorem.  The proof of the quotient
transport uses the standard full-subcategory creation lemma and the
equivalences of S1856/S1857; no colimit is fabricated.  Only propext,
Classical.choice and Quot.sound occur; see the audit block.

The mono obstruction is not just bookkeeping: a monomorphism of the full
subcategory S1856StrictSub need not be a monomorphism of the ambient S1728
cover category, so S1791's mono complement theorem cannot be applied to the
underlying ambient map without an additional argument.  The direct route
therefore states the component factorization for that underlying map, which is
strictly stronger than S1791's mono-only API.  The essential-image route would
close this gap by making the forgetful functor an equivalence, but it is not
proved in the tree.
-/

import tmp.sheaf.xif.paper.S1857CoherentLimits01Actual
import tmp.sheaf.xif.paper.S1815AffineQuotientColimitsActual
import tmp.sheaf.xif.paper.S1791MonoComplementActual
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1867CoherentQuotientsActual

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual
open LeanFormal.IUT.XiFPaper.S1791MonoComplementActual
open LeanFormal.IUT.XiFPaper.S1792QuotientCoverActual
open LeanFormal.IUT.XiFPaper.S1815AffineQuotientColimitsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual

universe u v w uC vC

attribute [local instance] S1728ActualCategory11 S1854CoherentCategory11

/-! ## 1. Quotients on the strict image of the coherent covers -/

section StrictQuotients

variable {J : Type u} [Category.{v} J]

/-- The exact apex-coherence input: the ambient S1728 colimit apex of every
J-shaped diagram of strict coherent covers is isomorphic to a strict object. -/
def S1867QuotientApexCoherent
    (Q : (D : J ⥤ S1728Cover) → ColimitCocone D) : Prop :=
  ∀ D : J ⥤ S1856StrictSub,
    Nonempty { P : S1856StrictSub //
      Nonempty ((Q (D ⋙ S1856StrictProperty.ι)).cocone.pt ≅ P.obj) }

/-- **Colimits of the strict image from ambient colimits with coherent
apexes.**  The ambient colimit is extended along the apex isomorphism to a
cocone whose point lies in the strict image; the full-subcategory inclusion
then creates the colimit. -/
theorem S1867HasColimitsOfShapeStrict
    (Q : (D : J ⥤ S1728Cover) → ColimitCocone D)
    (hA : S1867QuotientApexCoherent Q) :
    HasColimitsOfShape J S1856StrictSub := by
  refine ⟨fun D => ?_⟩
  obtain ⟨P, ⟨e⟩⟩ := hA D
  let c0 := (Q (D ⋙ S1856StrictProperty.ι)).cocone
  let hc0 := (Q (D ⋙ S1856StrictProperty.ι)).isColimit
  let cExt := c0.extend e.hom
  have hcExt : IsColimit cExt := IsColimit.extendIso e.hom hc0
  haveI : HasColimit (D ⋙ S1856StrictProperty.ι) :=
    HasColimit.mk ⟨c0, hc0⟩
  letI : CreatesColimit D S1856StrictProperty.ι :=
    createsColimitFullSubcategoryInclusion' D hcExt P.property
  exact hasColimit_of_created D S1856StrictProperty.ι

/-- **Quotients on the actual coherent category** from ambient colimits with
coherent apexes.  This is the transport across the equivalence
S1856ToStrict of the strict-image colimits. -/
theorem S1867HasColimitsOfShape11
    (Q : (D : J ⥤ S1728Cover) → ColimitCocone D)
    (hA : S1867QuotientApexCoherent Q) :
    @HasColimitsOfShape J _ CoherentCover S1854CoherentCategory11 :=
  @Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 S1856StrictSub _
    J _ S1856ToStrict S1856ToStrict_isEquivalence
    (S1867HasColimitsOfShapeStrict Q hA)

end StrictQuotients

/-! ## 2. The S1792 quotient cocones and the precise first missing -/

/-- The S1792 finite-group quotient cocone, using S1815's proof of the affine
quotient colimits.  This is the actual quotient construction, not a new one. -/
noncomputable def S1867QuotientCocone11
    (E : S1792Cover ≌ S1792Slice) (G : Type 1) [Group G] [Finite G]
    (D : SingleObj G ⥤ S1728Cover) : ColimitCocone D :=
  ⟨S1792QuotientCocone E S1815AffineQuotientColimits G D,
   S1792QuotientCocone_isColimit E S1815AffineQuotientColimits G D⟩

/-- The apex coherence of the actual S1792 quotient covers. -/
def S1867QuotientApexCoherent11 (E : S1792Cover ≌ S1792Slice) : Prop :=
  ∀ (G : Type 1) [Group G] [Finite G],
    S1867QuotientApexCoherent (J := SingleObj G)
      (fun D => S1867QuotientCocone11 E G D)

/-- **Finite-group quotients on the coherent Category.{1,1}**, from an
S1792 cover-slice equivalence and the coherence of the actual quotient apexes. -/
theorem S1867HasQuotientsByFiniteGroups11
    (E : S1792Cover ≌ S1792Slice)
    (hA : S1867QuotientApexCoherent11 E) :
    ∀ (G : Type 1) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) (SingleObj.category G)
        CoherentCover S1854CoherentCategory11 := by
  intro G _ _
  exact S1867HasColimitsOfShape11 (J := SingleObj G)
    (fun D => S1867QuotientCocone11 E G D) (hA G)

/-- **The exact first missing for finite-group quotients on the coherent
Category.{1,1}.**  The first component is S1792's cover-slice comparison; the
second is the coherence of the actual quotient apexes.  S1815 already supplies
the affine quotient colimits, so they are not part of the missing data. -/
def S1867QuotientFirstMissing11 : Prop :=
  ∃ E : S1792Cover ≌ S1792Slice, S1867QuotientApexCoherent11 E

/-- The exact first missing suffices for the quotient field at
S1854CoherentCategory11. -/
theorem S1867HasQuotientsByFiniteGroups11_of_firstMissing
    (h : S1867QuotientFirstMissing11) :
    ∀ (G : Type 1) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) (SingleObj.category G)
        CoherentCover S1854CoherentCategory11 := by
  rcases h with ⟨E, hA⟩
  exact S1867HasQuotientsByFiniteGroups11 E hA


/-! ## 3. The target-universe (Type 0) quotient cocones -/

/-- The finite-group quotient cocone at the target universe.  The affine
finite-etale algebra side has quotient colimits by S1815's general fixed-point
theorem; the slice equivalence and the S1792 cover-slice equivalence transport
them to the actual cover category. -/
noncomputable def S1867QuotientCocone01
    (E : S1792Cover ≌ S1792Slice) (G : Type) [Group G] [Finite G]
    (D : SingleObj G ⥤ S1728Cover) : ColimitCocone D := by
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  haveI hAlg : HasColimitsOfShape (SingleObj G) (Slice.Algᵒᵖ) :=
    General.hasColimitsOfShape_finiteEtaleAlg (R := Slice.R) (G := G)
  haveI hSlice : HasColimitsOfShape (SingleObj G) S1733Slice :=
    @Adjunction.hasColimitsOfShape_of_equivalence
      S1733Slice _ (Slice.Algᵒᵖ) _ (SingleObj G) (SingleObj.category G)
      Slice.sliceEquivalence.inverse _ hAlg
  haveI hCover : HasColimitsOfShape (SingleObj G) S1728Cover :=
    @Adjunction.hasColimitsOfShape_of_equivalence
      S1728Cover _ S1733Slice _ (SingleObj G) (SingleObj.category G)
      E.functor _ hSlice
  exact Classical.choice (hCover.has_colimit D).exists_colimit

/-- The apex coherence of the target-universe quotient cocones. -/
def S1867QuotientApexCoherent01 (E : S1792Cover ≌ S1792Slice) : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    S1867QuotientApexCoherent (J := SingleObj G)
      (fun D => S1867QuotientCocone01 E G D)

/-- Finite-group quotients on the coherent Category.{1,1} at Type-0 group
universes, from the target-universe quotient cocones. -/
theorem S1867HasQuotientsByFiniteGroups11Zero
    (E : S1792Cover ≌ S1792Slice)
    (hA : S1867QuotientApexCoherent01 E) :
    ∀ (G : Type) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) (SingleObj.category G)
        CoherentCover S1854CoherentCategory11 := by
  intro G _ _
  exact S1867HasColimitsOfShape11 (J := SingleObj G)
    (fun D => S1867QuotientCocone01 E G D) (hA G)

section Quotients01

attribute [local instance] S1854CoherentCategory01

/-- **Finite-group quotients on the target coherent Category.{0,1}**, from the
Type-0 quotient cocones and their apex coherence. -/
theorem S1867HasQuotientsByFiniteGroups01
    (E : S1792Cover ≌ S1792Slice)
    (hA : S1867QuotientApexCoherent01 E) :
    ∀ (G : Type) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) (SingleObj.category G)
        CoherentCover S1854CoherentCategory01 := by
  intro G _ _
  exact @Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory01 CoherentCover S1854CoherentCategory11
    (SingleObj G) (SingleObj.category G)
    S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    (S1867HasQuotientsByFiniteGroups11Zero E hA G)

end Quotients01

/-- **The exact first missing for finite-group quotients at the target
universe.**  It is the same S1792 cover-slice comparison together with the
coherence of the Type-0 quotient apexes. -/
def S1867QuotientFirstMissing01 : Prop :=
  ∃ E : S1792Cover ≌ S1792Slice, S1867QuotientApexCoherent01 E

/-- The exact first missing suffices for the target-universe quotient field. -/
theorem S1867HasQuotientsByFiniteGroups01_of_firstMissing
    (h : S1867QuotientFirstMissing01) :
    ∀ (G : Type) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) (SingleObj.category G)
        CoherentCover S1854CoherentCategory01 := by
  rcases h with ⟨E, hA⟩
  exact S1867HasQuotientsByFiniteGroups01 E hA


/-! ## 4. The mono/direct-summand field: exact first missing -/

/-- S1791's component-factorization datum for the underlying ambient map of a
coherent mono.  It is stated for the ambient map because the categorical
complement construction of S1791 is purely categorical; the mono hypothesis of
S1791 is not used by that construction. -/
def S1867MonoComponentFactorization
    [HasFiniteCoproducts S1728Cover] : Prop :=
  ∀ {X Y : S1856StrictSub} (i : X ⟶ Y) [Mono i],
    S1791Abstract.MonoComponentFactorizationAPI (C := S1728Cover) i.hom

/-- The ambient complement apex of a coherent mono must be isomorphic to a
strict object. -/
def S1867MonoApexCoherent : Prop :=
  ∀ {X Y : S1856StrictSub} (i : X ⟶ Y) [Mono i]
    (Z : S1728Cover) (u : Z ⟶ Y.obj),
    Nonempty (IsColimit (BinaryCofan.mk i.hom u)) →
      Nonempty { P : S1856StrictSub // Nonempty (Z ≅ P.obj) }

/-- The direct S1791 first-missing package for the mono field: finite
coproducts, the component factorization of the underlying ambient maps, and
the mono apex coherence. -/
def S1867MonoFirstMissing : Prop :=
  ∃ h : HasFiniteCoproducts S1728Cover,
    @S1867MonoComponentFactorization h ∧ S1867MonoApexCoherent

/-- **The recorded transport implication for the mono field on the strict
image.**  It is not proved here.  The obstruction is that a monomorphism of
the full subcategory need not be a monomorphism of the ambient S1728 category,
so the S1791 ambient colimit cannot be reflected without an additional lift of
the complement leg. -/
def S1867MonoTransport : Prop :=
  S1867MonoFirstMissing →
    ∀ {X Y : S1856StrictSub} (i : X ⟶ Y) [Mono i],
      ∃ (Z : S1856StrictSub) (u : Z ⟶ Y),
        Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The essential-image gap: every ambient cover is isomorphic to the
underlying cover of a coherent cover.  This is stronger than the apex
conditions and would make the forgetful functor an equivalence, transporting
the whole S1728 PreGalois structure.  It is not proved here. -/
def S1867CoherentEssImage : Prop :=
  ∀ A : S1728Cover, ∃ C : CoherentCover, Nonempty (C.cover ≅ A)

/-- The equivalence-route first missing for the mono field: the essential-image
gap together with S1728's mono/direct-summand field. -/
def S1867MonoFirstMissingEss : Prop :=
  S1867CoherentEssImage ∧ S1763MonoDirectSummandData S1726K S1726Orbicurve

/-- **The recorded equivalence-route transport implication for the mono
field.**  It is not proved here; the standard equivalence transport of the
mono/direct-summand property is the remaining categorical step. -/
def S1867MonoTransportEss : Prop :=
  S1867MonoFirstMissingEss →
    ∀ {X Y : CoherentCover} (i : X ⟶ Y) [Mono i],
      ∃ (Z : CoherentCover) (u : Z ⟶ Y),
        Nonempty (IsColimit (BinaryCofan.mk i u))

/-! ## 5. Summary -/

/-- The quotient field at the target universe, from the S1792 cover-slice
equivalence and the Type-0 quotient apex coherence.  This is the proved part
of S1867. -/
theorem S1867Quotients01_proved
    (E : S1792Cover ≌ S1792Slice)
    (hA : S1867QuotientApexCoherent01 E) :
    ∀ (G : Type) [Group G] [Finite G],
      @HasColimitsOfShape (SingleObj G) (SingleObj.category G)
        CoherentCover S1854CoherentCategory01 :=
  S1867HasQuotientsByFiniteGroups01 E hA

/-- The exact remaining input for the quotient field at the target universe is
the conjunction of S1792's cover-slice comparison and the Type-0 quotient apex
coherence. -/
def S1867QuotientRemaining01 : Prop := S1867QuotientFirstMissing01

/-- The exact remaining input for the mono field, in the direct S1791 route. -/
def S1867MonoRemaining : Prop := S1867MonoFirstMissing

/-- The exact remaining input for the mono field, in the equivalence route. -/
def S1867MonoRemainingEss : Prop := S1867MonoFirstMissingEss


/-! ## 6. Checks and audit -/

#check S1867QuotientApexCoherent
#check S1867HasColimitsOfShapeStrict
#check S1867HasColimitsOfShape11
#check S1867QuotientCocone11
#check S1867QuotientApexCoherent11
#check S1867HasQuotientsByFiniteGroups11
#check S1867QuotientFirstMissing11
#check S1867HasQuotientsByFiniteGroups11_of_firstMissing
#check S1867QuotientCocone01
#check S1867QuotientApexCoherent01
#check S1867HasQuotientsByFiniteGroups11Zero
#check S1867HasQuotientsByFiniteGroups01
#check S1867QuotientFirstMissing01
#check S1867HasQuotientsByFiniteGroups01_of_firstMissing
#check S1867MonoComponentFactorization
#check S1867MonoApexCoherent
#check S1867MonoFirstMissing
#check S1867MonoTransport
#check S1867CoherentEssImage
#check S1867MonoFirstMissingEss
#check S1867MonoTransportEss
#check S1867Quotients01_proved
#check S1867QuotientRemaining01
#check S1867MonoRemaining
#check S1867MonoRemainingEss

#print axioms S1867HasColimitsOfShapeStrict
#print axioms S1867HasColimitsOfShape11
#print axioms S1867HasQuotientsByFiniteGroups11
#print axioms S1867HasQuotientsByFiniteGroups11_of_firstMissing
#print axioms S1867HasQuotientsByFiniteGroups01
#print axioms S1867HasQuotientsByFiniteGroups01_of_firstMissing
#print axioms S1867Quotients01_proved

end LeanFormal.IUT.XiFPaper.S1867CoherentQuotientsActual