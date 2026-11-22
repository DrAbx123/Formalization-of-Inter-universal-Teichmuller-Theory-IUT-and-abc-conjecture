import LeanFormal.IUT.Foundations.AlgebraicGeometry.CorrectedProviderGluing
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectQuotientEntry

/-!
# Corrected global quotient provider consumer

Consumes the actual corrected provider gluing (projection, action, invariant
square, chart/overlap equations, gluing desc/fac/uniq and IsColimit) together
with the project quotient entry consumer.  The result is the corrected global
quotient universal-property consumer; no residual-only variant is introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.ABCBridge.CorrectedQuotientActionActual
open _root_.ABCBridge.CorrectedProviderGluing
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectQuotientEntry
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

namespace ABCBridge.CorrectedGlobalProviderConsumer

universe u

variable {J : Type u} {G : Type u} [Group G]

/-- The corrected provider's covering chart family into the glued quotient. -/
def correctedProviderCover (HG : GluedQuotientData (J := J)) :
    J → (HG.V ⟶ HG.Q) :=
  HG.chart

/-- The corrected provider's projection is the actual identification map. -/
theorem correctedProviderCover_chart (HG : GluedQuotientData (J := J)) (i : J) :
    correctedProviderCover HG i = HG.chart i :=
  rfl

/-- Corrected global quotient provider data: cover, projection, equivariance,
chart/overlap equations, and gluing desc/fac/uniq. -/
structure CorrectedGlobalProviderUniversalProperty
    (HG : GluedQuotientData (J := J))
    (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q)
    (Z : Scheme.{u}) (c : GluingCocone HG Z) where
  cover : J → (HG.V ⟶ HG.Q)
  cover_eq_chart : ∀ i, cover i = HG.chart i
  projection : X ⟶ HG.Q
  projection_eq : projection = e.hom
  projection_invariant : ∀ g : G,
    ((providerActionData HG P e).coverAction g).hom ≫ projection =
      projection ≫ ((providerActionData HG P e).quotientAction g).hom
  chart_equation : ∀ (g : G) (i : J),
    HG.chart i ≫ ((providerActionData HG P e).quotientAction g).hom =
      HG.chart (P.sigma g i)
  overlap_equation : ∀ (g : G) (i j : J),
    HG.fst i j ≫ HG.chart i ≫ ((providerActionData HG P e).quotientAction g).hom =
      HG.snd i j ≫ HG.chart j ≫ ((providerActionData HG P e).quotientAction g).hom
  desc : HG.Q ⟶ Z
  desc_eq : desc = gluingDesc HG c
  desc_fac : ∀ i, HG.chart i ≫ desc = c.iota i
  desc_uniq : ∀ u : HG.Q ⟶ Z, (∀ i, HG.chart i ≫ u = c.iota i) → u = desc
  isColimit : ∃! u : HG.Q ⟶ Z, ∀ i, HG.chart i ≫ u = c.iota i

/-- The actual corrected global provider universal property. -/
noncomputable def correctedGlobalProviderUniversalProperty
    (HG : GluedQuotientData (J := J))
    (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q)
    (Z : Scheme.{u}) (c : GluingCocone HG Z) :
    CorrectedGlobalProviderUniversalProperty HG P e Z c where
  cover := correctedProviderCover HG
  cover_eq_chart := fun i => rfl
  projection := providerProjection HG e
  projection_eq := providerProjection_eq HG e
  projection_invariant := projection_invariant HG P e
  chart_equation := (providerActionData HG P e).chart_equation
  overlap_equation := (providerActionData HG P e).overlap_equation
  desc := gluingDesc HG c
  desc_eq := rfl
  desc_fac := fun i => gluingDesc_fac HG c i
  desc_uniq := fun u hu => gluingDesc_uniq HG c u hu
  isColimit := gluing_isColimit HG c

/-- The corrected global provider universal property is actual. -/
theorem correctedGlobalProviderUniversalProperty_holds
    (HG : GluedQuotientData (J := J))
    (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q)
    (Z : Scheme.{u}) (c : GluingCocone HG Z) :
    Nonempty (CorrectedGlobalProviderUniversalProperty HG P e Z c) :=
  ⟨correctedGlobalProviderUniversalProperty HG P e Z c⟩

/-- Affine-target and global glued-quotient components of the project entry
consumer, re-exposed for the corrected provider consumer. -/
theorem correctedGlobalProvider_projectEntry
    {R : Type u} [CommRing R]
    {G' : Type u} [Group G'] [Fintype G']
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G' A] [SMulCommClass G' R A]
    {S : Scheme.{u}} (D : LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty.GlobalGluedQuotientData S)
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G', specAction (R := R) (G := G') (A := A) g ≫ f = f)
    (Z : Scheme.{u}) (F : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hF : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ F i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ F j) :
    (∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G')) ⟶
        Spec (CommRingCat.of B),
      affineQuotientMap (R := R) (G := G') (A := A) ≫ u = f) ∧
      (∀ i : D.P.J,
        (D.P.toSchemeGlueData).ι i ≫ D.desc Z F hF = F i) ∧
      (∀ u : D.cover.carrier ⟶ Z,
        (∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = F i) →
          u = D.desc Z F hF) :=
  quotientEntryConsumer (R := R) (G := G') (A := A) D B f hf Z F hF

/-- Combined actual consumer: corrected global provider universal property and
the project quotient entry universal property. -/
noncomputable def correctedGlobalProvider_consumer
    (HG : GluedQuotientData (J := J))
    (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q)
    (Z : Scheme.{u}) (c : GluingCocone HG Z) :
    CorrectedGlobalProviderUniversalProperty HG P e Z c :=
  correctedGlobalProviderUniversalProperty HG P e Z c

/-- Corrected provider desc/fac/uniq consumer in primitive form. -/
theorem correctedGlobalProvider_desc_consumer
    (HG : GluedQuotientData (J := J))
    {Z : Scheme.{u}} (c : GluingCocone HG Z) :
    (∀ i, HG.chart i ≫ gluingDesc HG c = c.iota i) ∧
      (∀ u : HG.Q ⟶ Z, (∀ i, HG.chart i ≫ u = c.iota i) → u = gluingDesc HG c) ∧
      (∃! u : HG.Q ⟶ Z, ∀ i, HG.chart i ≫ u = c.iota i) :=
  ⟨fun i => gluingDesc_fac HG c i,
    fun u hu => gluingDesc_uniq HG c u hu,
    gluing_isColimit HG c⟩

/-- Corrected provider cover/projection consumer in primitive form. -/
theorem correctedGlobalProvider_cover_projection_consumer
    (HG : GluedQuotientData (J := J))
    (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (∀ i, correctedProviderCover HG i = HG.chart i) ∧
      providerProjection HG e = e.hom ∧
      (∀ g : G,
        ((providerActionData HG P e).coverAction g).hom ≫ providerProjection HG e =
          providerProjection HG e ≫ ((providerActionData HG P e).quotientAction g).hom) :=
  ⟨fun i => correctedProviderCover_chart HG i,
    providerProjection_eq HG e,
    fun g => projection_invariant HG P e g⟩

end ABCBridge.CorrectedGlobalProviderConsumer
