import tmp.sheaf.xif.paper.S2121ChoiceFreeLowerWitnessActual

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2124ToYEquationActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual
open LeanFormal.IUT.XiFPaper.S2114CanonicalLiftTwoCellActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual
open LeanFormal.IUT.XiFPaper.S2121ChoiceFreeLowerWitnessActual

universe u

/-! ## 1. rfl-unfoldings of the two comparison isomorphisms -/

section Unfold

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-- Right-associated unfolding of the first upper comparison. -/
theorem S2124LiftToYIsoX_hom {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom =
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).hom ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).symm.hom ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).symm.hom ≫
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).toX1)
          s.toX (S2121D f g T ptA Pg).x1
          (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
        s.commutes.hom := rfl

/-- Unfolding of the inverse of the first upper comparison, in the
right-associated form used by Coherence.S2114LowerLiftToACompat. -/
theorem S2124LiftToYIsoX_inv {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      s.commutes.inv ≫
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).toX1)
          s.toX (S2121D f g T ptA Pg).x1
          (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).inv ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).hom ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv := by
  have h : (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      ((((s.commutes.inv ≫
            (S2058WhiskerRightIso
              (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
                (S2121D f g T ptA Pg).toX1)
              s.toX (S2121D f g T ptA Pg).x1
              (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).inv) ≫
          (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom) ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).hom) ≫
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv := rfl
  rw [h]
  simp only [Category.assoc]

/-- Right-associated unfolding of the second upper comparison. -/
theorem S2124LiftToYIsoY_hom {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom =
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2).hom ≫
      (S2107ExtLiftToY2 (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom := rfl

/-- Right-associated unfolding of the inverse of the second upper comparison. -/
theorem S2124LiftToYIsoY_inv {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      (S2107ExtLiftToY2 (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv ≫
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2).inv := rfl

end Unfold

end LeanFormal.IUT.XiFPaper.S2124ToYEquationActual
