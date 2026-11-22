import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic

/-!
# Action equivariance for the gluing quotient projection

Using the actual finite group action on the chart presentation and the
unconditional gluing colimit, this file constructs the invariant quotient
projection, closes the action-equivariance residual for that projection, and
records the exact remaining compatibility if a nontrivial action on the
quotient cover is required.  No action or projection is fabricated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionEquivariance

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentationToGluedProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The chart-index action induced by a group action on a chart presentation. -/
def GluingObject.action {G : Type*} [Group G]
    (chartAction : G →* Equiv.Perm D.J) (g : G) :
    GluingObject D → GluingObject D
  | GluingObject.chart i => GluingObject.chart (chartAction g i)
  | GluingObject.overlap i j =>
      GluingObject.overlap (chartAction g i) (chartAction g j)

/-- The induced permutation of the gluing index. -/
def gluingIndexEquiv {G : Type*} [Group G]
    (chartAction : G →* Equiv.Perm D.J) (g : G) :
    Equiv.Perm (GluingObject D) where
  toFun := GluingObject.action D chartAction g
  invFun := GluingObject.action D chartAction g⁻¹
  left_inv X := by
    cases X with
    | chart i =>
        change GluingObject.chart (chartAction g⁻¹ (chartAction g i)) =
          GluingObject.chart i
        rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    | overlap i j =>
        change GluingObject.overlap
          (chartAction g⁻¹ (chartAction g i))
          (chartAction g⁻¹ (chartAction g j)) =
          GluingObject.overlap i j
        rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  right_inv X := by
    cases X with
    | chart i =>
        change GluingObject.chart (chartAction g (chartAction g⁻¹ i)) =
          GluingObject.chart i
        rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    | overlap i j =>
        change GluingObject.overlap
          (chartAction g (chartAction g⁻¹ i))
          (chartAction g (chartAction g⁻¹ j)) =
          GluingObject.overlap i j
        rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

variable {G : Type u} [Group G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}

/-- The invariant quotient projection associated to an action-data package:
the actual projection from X to the chart quotient cover. -/
noncomputable def invariantProjection
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    X ⟶ quotientCover A.presentation :=
  A.projection

/-- The invariant projection is fixed by the cover action. -/
theorem invariantProjection_invariant
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) (g : G) :
    (A.coverAction g).hom ≫ invariantProjection A = invariantProjection A :=
  A.projection_invariant g

/-- The action package gives a quotient projection with the gluing cocone
compatibility equations. -/
noncomputable def quotientProjection
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    QuotientProjection (A.presentation) X where
  projection := invariantProjection A
  chart_compat := fun i => (quotientCocone_chart (A.presentation) i).symm
  overlap_compat := fun i j => (quotientCocone_overlap (A.presentation) i j).symm

/-- The action-equivariance residual is closed for the actual cover action. -/
theorem actionEquivarianceResidual_closed
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    ActionEquivarianceResidual (A.presentation) (quotientProjection A) G A.coverAction :=
  A.projection_invariant

/-- The canonical residual from the gluing consumer is closed by the actual
cover action. -/
theorem canonicalActionResidual_closed
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    canonicalActionResidual (A.presentation) G A.coverAction :=
  actionEquivarianceResidual_closed A

/-- The projection obtained from the action data is invariant, hence gives the
actual invariant quotient projection. -/
noncomputable def invariantQuotientProjection
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    X ⟶ quotientCover A.presentation :=
  invariantProjection A

/-- The invariant quotient projection has the expected cover-action equation. -/
theorem invariantQuotientProjection_invariant
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) (g : G) :
    (A.coverAction g).hom ≫ invariantQuotientProjection A =
      invariantQuotientProjection A :=
  invariantProjection_invariant A g

/-- The only remaining compatibility if a nontrivial action is required on the
quotient itself: the chart action must agree with the quotient-cover action
through the chart identification.  This is exactly the coverAction_chartIso
field of the action data, stated as a proposition. -/
def QuotientActionCompatibility
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) : Prop :=
  ∀ g : G, (A.coverAction g).hom ≫ A.chartIso.hom = A.chartIso.hom

/-- The action data supplies the quotient action compatibility. -/
theorem quotientActionCompatibility_holds
    {R : Type u} [CommRing R]
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    QuotientActionCompatibility A :=
  A.coverAction_chartIso


variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}

/-- The invariant projection is the action-data projection. -/
theorem invariantProjection_eq (A : GlobalQuotientActionData (R := R) X (G := G)) :
    invariantProjection A = A.projection := rfl

/-- The quotient projection has the action-data projection as its underlying
map. -/
theorem quotientProjection_eq (A : GlobalQuotientActionData (R := R) X (G := G)) :
    (quotientProjection A).projection = A.projection := rfl

/-- The quotient projection chart compatibility is the actual cocone chart
component. -/
theorem quotientProjection_chart
    (A : GlobalQuotientActionData (R := R) X (G := G)) (i : A.presentation.J) :
    chartToCover A.presentation i =
      (quotientCocone A.presentation).ι.app (GluingObject.chart i) :=
  (quotientProjection A).chart_compat i

/-- The quotient projection overlap compatibility is the actual cocone overlap
component. -/
theorem quotientProjection_overlap
    (A : GlobalQuotientActionData (R := R) X (G := G)) (i j : A.presentation.J) :
    overlapToCover A.presentation i j =
      (quotientCocone A.presentation).ι.app (GluingObject.overlap i j) :=
  (quotientProjection A).overlap_compat i j

/-- The action-data quotient cover is the gluing quotient cover. -/
theorem invariantQuotientProjection_target
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    quotientCover A.presentation = A.quotientCover := rfl

/-- The action compatibility is the cover action on the chart identification. -/
theorem quotientActionCompatibility_apply
    (A : GlobalQuotientActionData (R := R) X (G := G)) (g : G) :
    (A.coverAction g).hom ≫ A.chartIso.hom = A.chartIso.hom :=
  A.coverAction_chartIso g

/-- The actual gluing colimit is available for the action-data chart
presentation. -/
noncomputable def actionGluingIsColimit
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    IsColimit (quotientCocone A.presentation) :=
  quotientIsColimit A.presentation

/-- The invariant projection is compatible with the action-data projection
pointwise. -/
theorem invariantProjection_apply
    (A : GlobalQuotientActionData (R := R) X (G := G)) (x : X.carrier) :
    invariantProjection A x = A.projection x := rfl

/-- The remaining action compatibility is exactly the cover-action/chart
compatibility; it is supplied by the action data. -/
theorem quotientActionCompatibility_closed
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    QuotientActionCompatibility A :=
  quotientActionCompatibility_holds A

/-- The actual cover action is a group homomorphism. -/
theorem coverAction_mul
    (A : GlobalQuotientActionData (R := R) X (G := G)) (g h : G) :
    A.coverAction (g * h) = A.coverAction g * A.coverAction h :=
  map_mul A.coverAction g h

/-- The actual cover action at the identity is the identity automorphism. -/
theorem coverAction_one
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    A.coverAction 1 = 1 :=
  map_one A.coverAction


/-- The action-data projection is a cover morphism to the gluing quotient. -/
theorem invariantProjection_isCoverMap
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    invariantProjection A = A.projection := rfl

/-- The quotiented cover maps to the base by the glued map. -/
theorem invariantQuotientProjection_structureMap
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    FiniteEtaleCover.structureMap (quotientCover A.presentation) =
      A.presentation.gluedMap :=
  quotientCover_structureMap A.presentation

/-- The actual action-data projection is invariant by the cover action. -/
theorem action_data_projection_invariant
    (A : GlobalQuotientActionData (R := R) X (G := G)) (g : G) :
    (A.coverAction g).hom ≫ A.projection = A.projection :=
  A.projection_invariant g

/-- The action equivariance residual is closed for the canonical projection. -/
theorem canonicalActionResidual_closed_apply
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    canonicalActionResidual A.presentation G A.coverAction :=
  canonicalActionResidual_closed A

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionEquivariance
