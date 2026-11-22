import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
import LeanFormal.IUT.Foundations.GlobalQuotientProvider
import Mathlib.Tactic

/-!
# Consumer of the gluing colimit

This file consumes the actual IsColimit of the gluing diagram.  It builds the
cover/cocone interface, exposes the gluing desc/fac/uniq, and packages a
quotient projection from a given cover.  Action equivariance is isolated as the
only remaining compatibility condition; no provider inhabitant is fabricated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentationToGluedProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProvider
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The actual quotient cover obtained from the gluing presentation. -/
noncomputable def quotientCover : FiniteEtaleCover S :=
  (toGluedData D).cover

/-- The quotient cover carrier is the glued scheme. -/
theorem quotientCover_carrier : (quotientCover D).carrier = D.glued := rfl

/-- The quotient cover structure map is the glued map. -/
theorem quotientCover_structureMap :
    FiniteEtaleCover.structureMap (quotientCover D) = D.gluedMap :=
  toGluedData_structureMap D

/-- The actual gluing cocone at the quotient cover point. -/
noncomputable def quotientCocone : Cocone (gluingDiagram D) :=
  gluingCocone D

/-- The gluing cocone is a colimit. -/
noncomputable def quotientIsColimit : IsColimit (quotientCocone D) :=
  gluingCocone_isColimit D

/-- The gluing desc map. -/
noncomputable def desc (c : Cocone (gluingDiagram D)) :
    (quotientCocone D).pt ⟶ c.pt :=
  (quotientIsColimit D).desc c

/-- Fac for the gluing desc map. -/
theorem desc_fac (c : Cocone (gluingDiagram D)) (X : GluingObject D) :
    (quotientCocone D).ι.app X ≫ desc D c = c.ι.app X :=
  (quotientIsColimit D).fac c X

/-- Uniqueness for the gluing desc map. -/
theorem desc_uniq (c : Cocone (gluingDiagram D)) (u : (quotientCocone D).pt ⟶ c.pt)
    (hu : ∀ X : GluingObject D, (quotientCocone D).ι.app X ≫ u = c.ι.app X) :
    u = desc D c :=
  (quotientIsColimit D).uniq c u hu

/-- The chart component of the quotient cocone. -/
theorem quotientCocone_chart (i : D.J) :
    (quotientCocone D).ι.app (GluingObject.chart i) = chartToCover D i :=
  gluingCocone_chart D i

/-- The overlap component of the quotient cocone. -/
theorem quotientCocone_overlap (i j : D.J) :
    (quotientCocone D).ι.app (GluingObject.overlap i j) = overlapToCover D i j :=
  gluingCocone_overlap D i j

/-- A quotient projection from an actual cover X to the quotient cover,
together with its compatibility with the chart/overlap cocone. -/
structure QuotientProjection
    (X : FiniteEtaleCover S) where
  projection : X ⟶ (quotientCover D)
  chart_compat : ∀ i : D.J,
    chartToCover D i = (quotientCocone D).ι.app (GluingObject.chart i)
  overlap_compat : ∀ i j : D.J,
    overlapToCover D i j = (quotientCocone D).ι.app (GluingObject.overlap i j)

/-- Every chart presentation has the canonical projection from its own cover,
with the chart compatibility equations holding definitionally. -/
noncomputable def canonicalProjection : QuotientProjection D (quotientCover D) where
  projection := 𝟙 _
  chart_compat := fun i => (quotientCocone_chart D i).symm
  overlap_compat := fun i j => (quotientCocone_overlap D i j).symm

/-- Provider interface assembled from the gluing colimit: cover, projection,
desc/fac/uniq and the actual IsColimit. -/
structure GlobalQuotientGluingProvider
    (X : FiniteEtaleCover S) where
  quotient : FiniteEtaleCover S
  projection : X ⟶ quotient
  cocone : Cocone (gluingDiagram D)
  isColimit : IsColimit cocone
  desc : ∀ c : Cocone (gluingDiagram D), cocone.pt ⟶ c.pt
  fac : ∀ (c : Cocone (gluingDiagram D)) (Y : GluingObject D),
    cocone.ι.app Y ≫ desc c = c.ι.app Y
  uniq : ∀ (c : Cocone (gluingDiagram D)) (u : cocone.pt ⟶ c.pt),
    (∀ Y : GluingObject D, cocone.ι.app Y ≫ u = c.ι.app Y) → u = desc c

/-- The actual provider interface for the quotient cover, with identity
projection from the quotient cover itself. -/
noncomputable def gluingProviderSelf :
    GlobalQuotientGluingProvider D (quotientCover D) where
  quotient := quotientCover D
  projection := 𝟙 _
  cocone := quotientCocone D
  isColimit := quotientIsColimit D
  desc := desc D
  fac := desc_fac D
  uniq := desc_uniq D

/-- The provider cover is the gluing quotient cover. -/
theorem gluingProviderSelf_quotient :
    (gluingProviderSelf D).quotient = quotientCover D := rfl

/-- The provider projection is the identity. -/
theorem gluingProviderSelf_projection :
    (gluingProviderSelf D).projection = 𝟙 _ := rfl

/-- The provider cocone is the quotient cocone. -/
theorem gluingProviderSelf_cocone :
    (gluingProviderSelf D).cocone = quotientCocone D := rfl

/-- The provider IsColimit is the actual gluing colimit. -/
theorem gluingProviderSelf_isColimit :
    (gluingProviderSelf D).isColimit = quotientIsColimit D := rfl

/-- The only remaining action input: a group action on the cover whose
projection is invariant.  This is a proposition, not an assumed provider. -/
def ActionEquivarianceResidual
    {X : FiniteEtaleCover S} (P : QuotientProjection D X)
    (G : Type u) [Group G]
    (action : G →* CategoryTheory.Aut X) : Prop :=
  ∀ g : G, (action g).hom ≫ P.projection = P.projection

/-- The action-equivariance residual is exactly the projection invariance. -/
theorem actionEquivarianceResidual_iff
    {X : FiniteEtaleCover S} (P : QuotientProjection D X)
    (G : Type u) [Group G]
    (action : G →* CategoryTheory.Aut X) :
    ActionEquivarianceResidual D P G action ↔
      ∀ g : G, (action g).hom ≫ P.projection = P.projection :=
  Iff.rfl

/-- The provider constructed from the gluing colimit has the actual desc maps. -/
theorem gluingProviderSelf_desc (c : Cocone (gluingDiagram D)) :
    (gluingProviderSelf D).desc c = desc D c := rfl

/-- The provider constructed from the gluing colimit has the actual fac
equations. -/
theorem gluingProviderSelf_fac (c : Cocone (gluingDiagram D)) (Y : GluingObject D) :
    (gluingProviderSelf D).cocone.ι.app Y ≫ (gluingProviderSelf D).desc c =
      c.ι.app Y :=
  desc_fac D c Y

/-- The provider constructed from the gluing colimit has the actual uniqueness. -/
theorem gluingProviderSelf_uniq (c : Cocone (gluingDiagram D))
    (u : (gluingProviderSelf D).cocone.pt ⟶ c.pt)
    (hu : ∀ Y : GluingObject D, (gluingProviderSelf D).cocone.ι.app Y ≫ u = c.ι.app Y) :
    u = (gluingProviderSelf D).desc c :=
  desc_uniq D c u hu


namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The quotient cover is finite etale over the base. -/
theorem quotientCover_finiteEtale :
    Etale (FiniteEtaleCover.structureMap (quotientCover D)) ∧
      IsFinite (FiniteEtaleCover.structureMap (quotientCover D)) :=
  toGluedData_finiteEtale D

/-- The quotient cover has the same carrier as the glued scheme. -/
theorem quotientCover_carrier_eq : (quotientCover D).carrier = D.glued := rfl

/-- The provider's canonical projection is a cover morphism. -/
theorem canonicalProjection_isCoverMap :
    (canonicalProjection D).projection = 𝟙 (quotientCover D) := rfl

/-- The canonical projection has the chart compatibility equations. -/
theorem canonicalProjection_chart (i : D.J) :
    chartToCover D i =
      (quotientCocone D).ι.app (GluingObject.chart i) :=
  (canonicalProjection D).chart_compat i

/-- The canonical projection has the overlap compatibility equations. -/
theorem canonicalProjection_overlap (i j : D.J) :
    overlapToCover D i j =
      (quotientCocone D).ι.app (GluingObject.overlap i j) :=
  (canonicalProjection D).overlap_compat i j

/-- A provider desc map is the gluing colimit desc. -/
theorem provider_desc_eq (X : FiniteEtaleCover S)
    (P : GlobalQuotientGluingProvider D X)
    (c : Cocone (gluingDiagram D)) :
    P.desc c = P.isColimit.desc c := rfl

/-- The provider desc restricts to each gluing object. -/
theorem provider_desc_fac (X : FiniteEtaleCover S)
    (P : GlobalQuotientGluingProvider D X)
    (c : Cocone (gluingDiagram D)) (Y : GluingObject D) :
    P.cocone.ι.app Y ≫ P.desc c = c.ι.app Y :=
  P.fac c Y

/-- The provider desc is unique. -/
theorem provider_desc_uniq (X : FiniteEtaleCover S)
    (P : GlobalQuotientGluingProvider D X)
    (c : Cocone (gluingDiagram D)) (u : P.cocone.pt ⟶ c.pt)
    (hu : ∀ Y : GluingObject D, P.cocone.ι.app Y ≫ u = c.ι.app Y) :
    u = P.desc c :=
  P.uniq c u hu

/-- The gluing provider has the chart fac equation in the form used by the
quotient consumer. -/
theorem gluingProviderSelf_chart_fac (c : Cocone (gluingDiagram D)) (i : D.J) :
    (quotientCocone D).ι.app (GluingObject.chart i) ≫
        (gluingProviderSelf D).desc c =
      c.ι.app (GluingObject.chart i) :=
  desc_fac D c (GluingObject.chart i)

/-- The gluing provider has the overlap fac equation. -/
theorem gluingProviderSelf_overlap_fac (c : Cocone (gluingDiagram D)) (i j : D.J) :
    (quotientCocone D).ι.app (GluingObject.overlap i j) ≫
        (gluingProviderSelf D).desc c =
      c.ι.app (GluingObject.overlap i j) :=
  desc_fac D c (GluingObject.overlap i j)

/-- The canonical action-equivariance condition is exactly projection
invariance; it is not asserted for any nontrivial action. -/
def canonicalActionResidual (G : Type u) [Group G]
    (action : G →* CategoryTheory.Aut (quotientCover D)) : Prop :=
  ActionEquivarianceResidual D (canonicalProjection D) G action

/-- The canonical action residual is the projection-invariance condition. -/
theorem canonicalActionResidual_iff (G : Type u) [Group G]
    (action : G →* CategoryTheory.Aut (quotientCover D)) :
    canonicalActionResidual D G action ↔
      ∀ g : G, (action g).hom ≫ (canonicalProjection D).projection =
        (canonicalProjection D).projection :=
  Iff.rfl

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
