import LeanFormal.IUT.Foundations.AlgebraicGeometry.CorrectedQuotientActionActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CorrectedActionProviderConsumer

/-!
# Project-facing corrected quotient action consumer

This module exposes the actual corrected quotient action constructed from chart
permutations, together with its chart and overlap equations, cocycle, comparison
square, and moved-chart nontriviality.  No action or equation is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.ProjectCorrectedQuotientAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ABCBridge.CorrectedQuotientActionActual
open ABCBridge.CorrectedActionProviderConsumer

universe u

variable {J : Type u} {G : Type u} [Group G]
  (HG : GluedQuotientData (J := J))
  (P : ChartPermutationData (HG := HG) (G := G))

/-- The actual corrected quotient action on the glued quotient. -/
noncomputable def projectCorrectedQuotientAction :
    G →* CategoryTheory.Aut HG.Q :=
  gluedAction HG P

theorem projectCorrectedQuotientAction_eq :
    projectCorrectedQuotientAction HG P = gluedAction HG P :=
  rfl

/-- The chart equation of the actual quotient action. -/
theorem projectCorrectedQuotientAction_chart (g : G) (i : J) :
    HG.chart i ≫ (projectCorrectedQuotientAction HG P g).hom =
      HG.chart (P.sigma g i) :=
  gluedAction_chart HG P g i

/-- The overlap equation of the actual quotient action. -/
theorem projectCorrectedQuotientAction_overlap (g : G) (i j : J) :
    HG.fst i j ≫ HG.chart i ≫ (projectCorrectedQuotientAction HG P g).hom =
      HG.snd i j ≫ HG.chart j ≫ (projectCorrectedQuotientAction HG P g).hom :=
  gluedAction_overlap HG P g i j

/-- The chart permutation cocycle. -/
theorem projectCorrectedQuotientAction_cocycle (g h : G) (i : J) :
    P.sigma (g * h) i = P.sigma g (P.sigma h i) :=
  P.sigma_mul g h i

/-- Nontriviality on the quotient from a moved separated chart. -/
theorem projectCorrectedQuotientAction_nontrivial_of_moved
    (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    projectCorrectedQuotientAction HG P g ≠ 1 :=
  gluedAction_nontrivial_of_moved_separated HG P g h

/-- The actual provider-consumer action data. -/
noncomputable def projectCorrectedProviderActionData
    {X : Scheme.{u}} (e : X ≅ HG.Q) :
    CorrectedProviderActionData HG P X e :=
  correctedProviderActionData HG P e

/-- The cover/quotient comparison square. -/
theorem projectCorrectedProviderAction_comparison
    {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G) :
    ((projectCorrectedProviderActionData HG P e).coverAction g).hom ≫ e.hom =
      e.hom ≫ ((projectCorrectedProviderActionData HG P e).quotientAction g).hom :=
  correctedProviderActionData_comparison HG P e g

/-- The cover action is nontrivial from a moved separated quotient chart. -/
theorem projectCorrectedProviderAction_nontrivial
    {X : Scheme.{u}} (e : X ≅ HG.Q) (g : G)
    (h : ∃ i : J, P.sigma g i ≠ i ∧ HG.chart i ≠ HG.chart (P.sigma g i)) :
    (projectCorrectedProviderActionData HG P e).coverAction g ≠ 1 :=
  correctedProviderActionData_cover_nontrivial HG P e g h

/-- Complete Project-facing package: chart, overlap, cocycle, and nontriviality
all come from the actual action. -/
theorem projectCorrectedQuotientAction_complete
    (g : G) (i j : J) :
    (HG.chart i ≫ (projectCorrectedQuotientAction HG P g).hom =
        HG.chart (P.sigma g i)) ∧
      (HG.fst i j ≫ HG.chart i ≫ (projectCorrectedQuotientAction HG P g).hom =
        HG.snd i j ≫ HG.chart j ≫ (projectCorrectedQuotientAction HG P g).hom) ∧
      (P.sigma (g * 1) i = P.sigma g (P.sigma 1 i)) :=
  ⟨projectCorrectedQuotientAction_chart HG P g i,
    projectCorrectedQuotientAction_overlap HG P g i j,
    projectCorrectedQuotientAction_cocycle HG P g 1 i⟩

end LeanFormal.IUT.ProjectCorrectedQuotientAction
end
