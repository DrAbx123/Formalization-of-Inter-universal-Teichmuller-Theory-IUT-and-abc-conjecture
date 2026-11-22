import LeanFormal.IUT.Foundations.AlgebraicGeometry.CorrectedActionProviderConsumer
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Corrected global quotient provider at the glued level

This file feeds the actual action data of CorrectedActionProviderConsumer into a
corrected provider.  It has the actual cover, projection, comparison square,
chart and overlap equations, and the gluing desc/fac/uniq universal property.  It
does not use the legacy GlobalQuotientActionData.
-/
namespace ABCBridge.CorrectedProviderGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ABCBridge.CorrectedQuotientActionActual
open ABCBridge.CorrectedActionProviderConsumer

universe u

variable {J : Type u} {G : Type u} [Group G]

/-- The actual projection from the cover to the glued quotient. -/
noncomputable def providerProjection
    (HG : GluedQuotientData (J := J)) {X : Scheme.{u}} (e : X ≅ HG.Q) :
    X ⟶ HG.Q :=
  e.hom

/-- The projection is the identification map. -/
theorem providerProjection_eq
    (HG : GluedQuotientData (J := J)) {X : Scheme.{u}} (e : X ≅ HG.Q) :
    providerProjection HG e = e.hom :=
  rfl

/-- The corrected provider action datum used by the provider. -/
noncomputable def providerActionData
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) :
    CorrectedProviderActionData HG P X e :=
  correctedProviderActionData HG P e

/-- The comparison/equivariance square of the actual projection. -/
theorem projection_invariant
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    ((providerActionData HG P e).coverAction g).hom ≫ providerProjection HG e =
      providerProjection HG e ≫ ((providerActionData HG P e).quotientAction g).hom :=
  (providerActionData HG P e).comparison g

/-- The corrected provider data at the glued level. -/
structure CorrectedProviderGluingData
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    (X : Scheme.{u}) (e : X ≅ HG.Q) where
  projection : X ⟶ HG.Q
  actionData : CorrectedProviderActionData HG P X e
  projection_invariant : ∀ g : G,
    (actionData.coverAction g).hom ≫ projection = projection ≫ (actionData.quotientAction g).hom
  chart_equation : ∀ (g : G) (i : J),
    HG.chart i ≫ (actionData.quotientAction g).hom = HG.chart (P.sigma g i)
  overlap_equation : ∀ (g : G) (i j : J),
    HG.fst i j ≫ HG.chart i ≫ (actionData.quotientAction g).hom =
      HG.snd i j ≫ HG.chart j ≫ (actionData.quotientAction g).hom

/-- The actual corrected provider from the identification e : X ≅ HG.Q. -/
noncomputable def correctedProviderGluingData
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) :
    CorrectedProviderGluingData HG P X e where
  projection := providerProjection HG e
  actionData := providerActionData HG P e
  projection_invariant := projection_invariant HG P e
  chart_equation := (providerActionData HG P e).chart_equation
  overlap_equation := (providerActionData HG P e).overlap_equation

/-- The provider projection is the actual projection. -/
theorem correctedProviderGluingData_projection
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderGluingData HG P e).projection = providerProjection HG e :=
  rfl

/-- The provider projection invariant square is actual. -/
theorem correctedProviderGluingData_projection_invariant
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    ((correctedProviderGluingData HG P e).actionData.coverAction g).hom ≫
        (correctedProviderGluingData HG P e).projection =
      (correctedProviderGluingData HG P e).projection ≫
        ((correctedProviderGluingData HG P e).actionData.quotientAction g).hom :=
  (correctedProviderGluingData HG P e).projection_invariant g

/-- The provider chart equation is actual. -/
theorem correctedProviderGluingData_chart
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i : J) :
    HG.chart i ≫
        ((correctedProviderGluingData HG P e).actionData.quotientAction g).hom =
      HG.chart (P.sigma g i) :=
  (correctedProviderGluingData HG P e).chart_equation g i

/-- The provider overlap equation is actual. -/
theorem correctedProviderGluingData_overlap
    (HG : GluedQuotientData (J := J)) (P : ChartPermutationData (HG := HG) (G := G))
    {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫
        ((correctedProviderGluingData HG P e).actionData.quotientAction g).hom =
      HG.snd i j ≫ HG.chart j ≫
        ((correctedProviderGluingData HG P e).actionData.quotientAction g).hom :=
  (correctedProviderGluingData HG P e).overlap_equation g i j

/-- The gluing cocone of a chart family in the glued quotient. -/
structure GluingCocone
    (HG : GluedQuotientData (J := J)) (Z : Scheme.{u}) where
  iota : J → (HG.V ⟶ Z)

/-- The gluing desc map from a chart family. -/
noncomputable def gluingDesc
    (HG : GluedQuotientData (J := J)) {Z : Scheme.{u}} (c : GluingCocone HG Z) :
    HG.Q ⟶ Z :=
  (HG.universal Z c.iota).choose

/-- The gluing desc map factors the chart family. -/
theorem gluingDesc_fac
    (HG : GluedQuotientData (J := J)) {Z : Scheme.{u}} (c : GluingCocone HG Z) (i : J) :
    HG.chart i ≫ gluingDesc HG c = c.iota i :=
  (HG.universal Z c.iota).choose_spec.1 i

/-- The gluing desc map is unique. -/
theorem gluingDesc_uniq
    (HG : GluedQuotientData (J := J)) {Z : Scheme.{u}} (c : GluingCocone HG Z)
    (u : HG.Q ⟶ Z) (hu : ∀ i, HG.chart i ≫ u = c.iota i) :
    u = gluingDesc HG c :=
  (HG.universal Z c.iota).choose_spec.2 u hu

/-- The gluing universal property: every chart family has a unique desc map. -/
theorem gluing_isColimit
    (HG : GluedQuotientData (J := J)) {Z : Scheme.{u}} (c : GluingCocone HG Z) :
    ∃! u : HG.Q ⟶ Z, ∀ i, HG.chart i ≫ u = c.iota i :=
  HG.universal Z c.iota

end ABCBridge.CorrectedProviderGluing