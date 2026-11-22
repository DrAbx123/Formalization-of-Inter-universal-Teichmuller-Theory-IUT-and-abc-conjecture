import LeanFormal.IUT.Foundations.AlgebraicGeometry.CorrectedQuotientActionActual
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Provider consumer for the corrected quotient action

The actual action gluedAction on HG.Q is transported along an identification
e : X ≅ HG.Q to a cover-level action on X.  The comparison square is proved, and
the chart/overlap equations and cocycle are inherited from the actual action.
No action or comparison is assumed.
-/
namespace ABCBridge.CorrectedActionProviderConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ABCBridge.CorrectedQuotientActionActual

universe u

variable {J : Type u} {G : Type u} [Group G]
  (HG : GluedQuotientData (J := J))
  (P : ChartPermutationData (HG := HG) (G := G))

/-- The actual glued action on the quotient scheme. -/
noncomputable def quotientAction : G →* CategoryTheory.Aut HG.Q :=
  gluedAction HG P

/-- The quotient action is the actual glued action. -/
theorem quotientAction_eq : quotientAction HG P = gluedAction HG P :=
  rfl

/-- The cover-level action transported from the quotient action along an
identification e : X ≅ HG.Q. -/
noncomputable def coverAction {X : Scheme.{u}} (e : X ≅ HG.Q) :
    G →* CategoryTheory.Aut X :=
  (CategoryTheory.Aut.autMulEquivOfIso e.symm).toMonoidHom.comp (gluedAction HG P)

/-- The cover action is the conjugate of the quotient action. -/
theorem coverAction_apply {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    (coverAction HG P e g).hom = e.hom ≫ (gluedAction HG P g).hom ≫ e.inv :=
  rfl

/-- The actual comparison square between the cover action and the quotient
action. -/
theorem coverAction_comparison {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    (coverAction HG P e g).hom ≫ e.hom =
      e.hom ≫ (gluedAction HG P g).hom := by
  rw [coverAction_apply]
  simp [Category.assoc]

/-- The cover action inherits the chart permutation cocycle. -/
theorem coverAction_cocycle (g h : G) (i : J) :
    P.sigma (g * h) i = P.sigma g (P.sigma h i) :=
  P.sigma_mul g h i

/-- The actual provider action datum for the existing provider consumer: cover
action on X, quotient action on HG.Q, comparison square, chart/overlap equations
and cocycle. -/
structure CorrectedProviderActionData (X : Scheme.{u}) (e : X ≅ HG.Q) where
  coverAction : G →* CategoryTheory.Aut X
  quotientAction : G →* CategoryTheory.Aut HG.Q
  coverAction_eq : coverAction = ABCBridge.CorrectedActionProviderConsumer.coverAction HG P e
  quotientAction_eq : quotientAction = gluedAction HG P
  comparison : ∀ g : G,
    (coverAction g).hom ≫ e.hom = e.hom ≫ (quotientAction g).hom
  chart_equation : ∀ (g : G) (i : J),
    HG.chart i ≫ (quotientAction g).hom = HG.chart (P.sigma g i)
  overlap_equation : ∀ (g : G) (i j : J),
    HG.fst i j ≫ HG.chart i ≫ (quotientAction g).hom =
      HG.snd i j ≫ HG.chart j ≫ (quotientAction g).hom

/-- The actual provider action data from the identification. -/
noncomputable def correctedProviderActionData {X : Scheme.{u}} (e : X ≅ HG.Q) :
    CorrectedProviderActionData HG P X e where
  coverAction := coverAction HG P e
  quotientAction := gluedAction HG P
  coverAction_eq := rfl
  quotientAction_eq := rfl
  comparison := coverAction_comparison HG P e
  chart_equation := gluedAction_chart HG P
  overlap_equation := gluedAction_overlap HG P

/-- The provider cover action is the transported glued action. -/
theorem correctedProviderActionData_coverAction {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderActionData HG P e).coverAction = coverAction HG P e :=
  rfl

/-- The provider quotient action is the actual glued action. -/
theorem correctedProviderActionData_quotientAction {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderActionData HG P e).quotientAction = gluedAction HG P :=
  rfl

/-- The provider comparison square. -/
theorem correctedProviderActionData_comparison {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    ((correctedProviderActionData HG P e).coverAction g).hom ≫ e.hom =
      e.hom ≫ ((correctedProviderActionData HG P e).quotientAction g).hom :=
  (correctedProviderActionData HG P e).comparison g

/-- The provider chart equation. -/
theorem correctedProviderActionData_chart {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i : J) :
    HG.chart i ≫ ((correctedProviderActionData HG P e).quotientAction g).hom =
      HG.chart (P.sigma g i) :=
  (correctedProviderActionData HG P e).chart_equation g i

/-- The provider overlap equation. -/
theorem correctedProviderActionData_overlap {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ ((correctedProviderActionData HG P e).quotientAction g).hom =
      HG.snd i j ≫ HG.chart j ≫
        ((correctedProviderActionData HG P e).quotientAction g).hom :=
  (correctedProviderActionData HG P e).overlap_equation g i j

/-- The provider action cocycle. -/
theorem correctedProviderActionData_cocycle (g h : G) (i : J) :
    P.sigma (g * h) i = P.sigma g (P.sigma h i) :=
  P.sigma_mul g h i

/-- Nontriviality transfers from the quotient action to the cover action. -/
theorem correctedProviderActionData_nontrivial {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G)
    (h : gluedAction HG P g ≠ 1) :
    (correctedProviderActionData HG P e).coverAction g ≠ 1 := by
  intro hcover
  have hcover' : coverAction HG P e g = 1 := by
    rw [← (correctedProviderActionData HG P e).coverAction_eq]
    exact hcover
  apply h
  have hconj : (CategoryTheory.Aut.autMulEquivOfIso e.symm)
      (gluedAction HG P g) = 1 := by
    simpa [coverAction] using hcover'
  exact (CategoryTheory.Aut.autMulEquivOfIso e.symm).injective (by simpa using hconj)

/-- The actual provider action datum is complete: cover action, quotient action,
comparison, chart/overlap equations and cocycle. -/
theorem correctedProviderActionData_complete {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) (i j : J) :
    (coverAction HG P e g).hom ≫ e.hom = e.hom ≫ (gluedAction HG P g).hom ∧
      HG.chart i ≫ (gluedAction HG P g).hom = HG.chart (P.sigma g i) ∧
      HG.fst i j ≫ HG.chart i ≫ (gluedAction HG P g).hom =
        HG.snd i j ≫ HG.chart j ≫ (gluedAction HG P g).hom :=
  ⟨coverAction_comparison HG P e g,
    gluedAction_chart HG P g i,
    gluedAction_overlap HG P g i j⟩


section ProviderActionProjections

/-- The cover action is multiplicative. -/
theorem correctedProviderActionData_coverAction_map_mul {X : Scheme.{u}} (e : X ≅ HG.Q) (g h : G) :
    (correctedProviderActionData HG P e).coverAction (g * h) =
      (correctedProviderActionData HG P e).coverAction g *
        (correctedProviderActionData HG P e).coverAction h :=
  map_mul (correctedProviderActionData HG P e).coverAction g h

/-- The cover action at the identity. -/
theorem correctedProviderActionData_coverAction_map_one {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderActionData HG P e).coverAction 1 = 1 :=
  map_one (correctedProviderActionData HG P e).coverAction

/-- The quotient action is multiplicative. -/
theorem correctedProviderActionData_quotientAction_map_mul {X : Scheme.{u}} (e : X ≅ HG.Q) (g h : G) :
    (correctedProviderActionData HG P e).quotientAction (g * h) =
      (correctedProviderActionData HG P e).quotientAction g *
        (correctedProviderActionData HG P e).quotientAction h :=
  map_mul (correctedProviderActionData HG P e).quotientAction g h

/-- The quotient action at the identity. -/
theorem correctedProviderActionData_quotientAction_map_one {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderActionData HG P e).quotientAction 1 = 1 :=
  map_one (correctedProviderActionData HG P e).quotientAction

/-- The provider comparison at the identity. -/
theorem correctedProviderActionData_comparison_one {X : Scheme.{u}} (e : X ≅ HG.Q) :
    ((correctedProviderActionData HG P e).coverAction 1).hom ≫ e.hom =
      e.hom ≫ ((correctedProviderActionData HG P e).quotientAction 1).hom :=
  (correctedProviderActionData HG P e).comparison 1

/-- The provider chart equation at the identity. -/
theorem correctedProviderActionData_chart_one {X : Scheme.{u}} (e : X ≅ HG.Q) (i : J) :
    HG.chart i ≫ ((correctedProviderActionData HG P e).quotientAction 1).hom =
      HG.chart (P.sigma 1 i) :=
  (correctedProviderActionData HG P e).chart_equation 1 i

/-- The provider overlap equation at the identity. -/
theorem correctedProviderActionData_overlap_one {X : Scheme.{u}} (e : X ≅ HG.Q) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ ((correctedProviderActionData HG P e).quotientAction 1).hom =
      HG.snd i j ≫ HG.chart j ≫ ((correctedProviderActionData HG P e).quotientAction 1).hom :=
  (correctedProviderActionData HG P e).overlap_equation 1 i j

/-- The provider quotient action is the actual glued action. -/
theorem correctedProviderActionData_quotientAction_eq {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderActionData HG P e).quotientAction = gluedAction HG P :=
  (correctedProviderActionData HG P e).quotientAction_eq

/-- The provider cover action is the transported glued action. -/
theorem correctedProviderActionData_coverAction_eq {X : Scheme.{u}} (e : X ≅ HG.Q) :
    (correctedProviderActionData HG P e).coverAction = coverAction HG P e :=
  (correctedProviderActionData HG P e).coverAction_eq

/-- The provider action has the chart permutation cocycle. -/
theorem correctedProviderActionData_cocycle_apply (g h : G) (i : J) :
    P.sigma (g * h) i = P.sigma g (P.sigma h i) :=
  P.sigma_mul g h i

/-- The actual action is nontrivial on the quotient from a moved separated chart. -/
theorem correctedProviderActionData_quotient_nontrivial (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    gluedAction HG P g ≠ 1 :=
  gluedAction_nontrivial_of_moved_separated HG P g h

/-- The actual action is nontrivial on the cover from a moved separated chart. -/
theorem correctedProviderActionData_cover_nontrivial {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    (correctedProviderActionData HG P e).coverAction g ≠ 1 :=
  correctedProviderActionData_nontrivial HG P e g (gluedAction_nontrivial_of_moved_separated HG P g h)

/-- The provider action package has no residual fields: all equations are actual. -/
theorem correctedProviderActionData_actual {X : Scheme.{u}} (e : X ≅ HG.Q) :
    Nonempty (CorrectedProviderActionData HG P X e) :=
  ⟨correctedProviderActionData HG P e⟩

end ProviderActionProjections

end ABCBridge.CorrectedActionProviderConsumer