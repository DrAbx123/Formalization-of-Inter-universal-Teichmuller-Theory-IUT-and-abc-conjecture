import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1801LiftEssSurjActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2120PresentationTwistActual

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
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u

def S2120StrongPresentationTwist : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
    let c0 := S2118Conv f g T ptA Pg.toWeak s
    Pseudofunctor.StrongTrans.whiskerRight (Pg.toWeak.isPullback.liftToX W c0).hom g.map ≫
        c0.commutes.hom =
      (S2107ImageCone (S2118PresentationSquare f g T ptA Pg.toWeak)
          (Pg.toWeak.isPullback.lift W c0)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (Pg.toWeak.isPullback.liftToY W c0).hom
          (Pseudofunctor.StrongTrans.vcomp ptA f.map)

theorem S2120StrongPresentationTwist_of_S2118 (h : S2118PresentationTwist) :
    S2120StrongPresentationTwist := by
  intro A B C f g T ptA Pg W s
  exact h A B C f g T ptA Pg.toWeak W s

end LeanFormal.IUT.XiFPaper.S2120PresentationTwistActual
