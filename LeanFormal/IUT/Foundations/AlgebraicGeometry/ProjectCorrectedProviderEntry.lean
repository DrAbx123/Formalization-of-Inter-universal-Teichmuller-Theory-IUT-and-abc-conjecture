import LeanFormal.IUT.Foundations.AlgebraicGeometry.CorrectedProviderGluing
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectCorrectedQuotientAction

/-!
# Project-facing corrected provider entry

This module exposes the actual corrected provider projection, invariance square,
gluing desc/fac/uniq property, and chart/overlap equations.  It consumes the
green CorrectedProviderGluing module and the existing ProjectCorrectedQuotientAction
consumer.  No action, projection, or equation is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.ProjectCorrectedProviderEntry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ABCBridge.CorrectedQuotientActionActual
open ABCBridge.CorrectedProviderGluing
open LeanFormal.IUT.ProjectCorrectedQuotientAction

universe u

variable {J : Type u} {G : Type u} [Group G]
  (HG : GluedQuotientData (J := J))
  (P : ChartPermutationData (HG := HG) (G := G))

/-- The actual corrected provider projection to the glued quotient. -/
noncomputable def projectCorrectedProviderProjection {X : Scheme.{u}} (e : X ≅ HG.Q) :
    X ⟶ HG.Q :=
  providerProjection HG e

/-- The projection is the identification map. -/
theorem projectCorrectedProviderProjection_eq {X : Scheme.{u}} (e : X ≅ HG.Q) :
    projectCorrectedProviderProjection HG e = e.hom :=
  rfl

/-- The actual corrected provider data. -/
noncomputable def projectCorrectedProviderData {X : Scheme.{u}} (e : X ≅ HG.Q) :
    CorrectedProviderGluingData HG P X e :=
  correctedProviderGluingData HG P e

/-- The provider projection invariance square. -/
theorem projectCorrectedProvider_projection_invariant {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    ((projectCorrectedProviderData HG P e).actionData.coverAction g).hom ≫
        (projectCorrectedProviderData HG P e).projection =
      (projectCorrectedProviderData HG P e).projection ≫
        ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom :=
  (projectCorrectedProviderData HG P e).projection_invariant g

/-- The provider chart equation. -/
theorem projectCorrectedProvider_chart {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i : J) :
    HG.chart i ≫
        ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom =
      HG.chart (P.sigma g i) :=
  (projectCorrectedProviderData HG P e).chart_equation g i

/-- The provider overlap equation. -/
theorem projectCorrectedProvider_overlap {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫
        ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom =
      HG.snd i j ≫ HG.chart j ≫
        ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom :=
  (projectCorrectedProviderData HG P e).overlap_equation g i j

/-- The corrected provider quotient action is the actual glued action. -/
theorem projectCorrectedProvider_quotientAction {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (projectCorrectedProviderData HG P e).actionData.quotientAction = gluedAction HG P :=
  (projectCorrectedProviderData HG P e).actionData.quotientAction_eq

/-- The gluing desc map for a chart family. -/
noncomputable def projectCorrectedProviderDesc {Z : Scheme.{u}} (c : GluingCocone HG Z) :
    HG.Q ⟶ Z :=
  gluingDesc HG c

/-- The desc map factors the chart family. -/
theorem projectCorrectedProviderDesc_fac {Z : Scheme.{u}} (c : GluingCocone HG Z) (i : J) :
    HG.chart i ≫ projectCorrectedProviderDesc HG c = c.iota i :=
  gluingDesc_fac HG c i

/-- The desc map is unique. -/
theorem projectCorrectedProviderDesc_uniq {Z : Scheme.{u}} (c : GluingCocone HG Z)
    (u : HG.Q ⟶ Z) (hu : ∀ i, HG.chart i ≫ u = c.iota i) :
    u = projectCorrectedProviderDesc HG c :=
  gluingDesc_uniq HG c u hu

/-- The gluing universal property for the corrected provider. -/
theorem projectCorrectedProvider_isColimit {Z : Scheme.{u}} (c : GluingCocone HG Z) :
    ∃! u : HG.Q ⟶ Z, ∀ i, HG.chart i ≫ u = c.iota i :=
  gluing_isColimit HG c

/-- Complete Project-facing provider package: projection, invariance, chart,
overlap, desc, fac, and uniq. -/
theorem projectCorrectedProvider_complete {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i j : J)
    {Z : Scheme.{u}} (c : GluingCocone HG Z) :
    (projectCorrectedProviderProjection HG e = e.hom) ∧
      (((projectCorrectedProviderData HG P e).actionData.coverAction g).hom ≫
          (projectCorrectedProviderData HG P e).projection =
        (projectCorrectedProviderData HG P e).projection ≫
          ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom) ∧
      (HG.chart i ≫
          ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom =
        HG.chart (P.sigma g i)) ∧
      (HG.fst i j ≫ HG.chart i ≫
          ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom =
        HG.snd i j ≫ HG.chart j ≫
          ((projectCorrectedProviderData HG P e).actionData.quotientAction g).hom) ∧
      (HG.chart i ≫ projectCorrectedProviderDesc HG c = c.iota i) :=
  ⟨projectCorrectedProviderProjection_eq HG e,
    projectCorrectedProvider_projection_invariant HG P e g,
    projectCorrectedProvider_chart HG P e g i,
    projectCorrectedProvider_overlap HG P e g i j,
    projectCorrectedProviderDesc_fac HG c i⟩

end LeanFormal.IUT.ProjectCorrectedProviderEntry
