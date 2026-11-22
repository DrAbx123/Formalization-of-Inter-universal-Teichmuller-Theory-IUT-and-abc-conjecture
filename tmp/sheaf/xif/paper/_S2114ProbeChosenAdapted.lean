

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace LeanFormal.IUT.XiFPaper.S2114ProbeChosen
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
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual

universe u

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-- explicit toA theorem -/
theorem toAexplicit {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2114ProbeChosenBase.S2114D f g T ptA Pg).square1.Cone W}
    (m : (S2114ProbeChosenBase.S2114D f g T ptA Pg).square1.ConeMorphism s t) :
    (S2114ProbeChosenBase.S2114PastedTwoCell f g T ptA Pg m ▷
        (S2114ProbeChosenBase.S2114D f g T ptA Pg).square1.toY) ▷
        (S2114ProbeChosenBase.S2114D f g T ptA Pg).xi =
      ((α_ (S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
            (S2114ProbeChosenBase.S2114WP f g T ptA Pg) s)
          (S2114ProbeChosenBase.S2114D f g T ptA Pg).square1.toY
          (S2114ProbeChosenBase.S2114D f g T ptA Pg).xi).hom ≫
        S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
            (S2114ProbeChosenBase.S2114WP f g T ptA Pg) s ◁
          (S2114ProbeChosenBase.S2114D f g T ptA Pg).c1.inv ≫
          (α_ (S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
              (S2114ProbeChosenBase.S2114WP f g T ptA Pg) s)
            (S2114ProbeChosenBase.S2114D f g T ptA Pg).toX1
            (S2114ProbeChosenBase.S2114D f g T ptA Pg).x1).inv ≫
            (S2107ExtLiftToX (S2114ProbeChosenBase.S2114D f g T ptA Pg)
              (S2114ProbeChosenBase.S2114WP f g T ptA Pg) s).hom ▷
              (S2114ProbeChosenBase.S2114D f g T ptA Pg).x1 ≫
              s.commutes.hom) ≫
      m.toY ▷ (S2114ProbeChosenBase.S2114D f g T ptA Pg).xi ≫
        t.commutes.inv ≫
          (S2107ExtLiftToX (S2114ProbeChosenBase.S2114D f g T ptA Pg)
              (S2114ProbeChosenBase.S2114WP f g T ptA Pg) t).inv ▷
              (S2114ProbeChosenBase.S2114D f g T ptA Pg).x1 ≫
            (α_ (S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
                (S2114ProbeChosenBase.S2114WP f g T ptA Pg) t)
              (S2114ProbeChosenBase.S2114D f g T ptA Pg).toX1
              (S2114ProbeChosenBase.S2114D f g T ptA Pg).x1).hom ≫
              S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
                  (S2114ProbeChosenBase.S2114WP f g T ptA Pg) t ◁
                (S2114ProbeChosenBase.S2114D f g T ptA Pg).c1.hom ≫
                (α_ (S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
                    (S2114ProbeChosenBase.S2114WP f g T ptA Pg) t)
                  (S2114ProbeChosenBase.S2114D f g T ptA Pg).square1.toY
                  (S2114ProbeChosenBase.S2114D f g T ptA Pg).xi).inv :=
  LeanFormal.IUT.XiFPaper.S2114ProbeChosenBase.Coherence.S2114LowerLiftToACompat
    (Bc := EtaleStackPseudofunctor S1726K)
    (l_s := S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
      (S2114ProbeChosenBase.S2114WP f g T ptA Pg) s)
    (l_t := S2107ExtLift (S2114ProbeChosenBase.S2114D f g T ptA Pg)
      (S2114ProbeChosenBase.S2114WP f g T ptA Pg) t)
    (wtc := S2114ProbeChosenBase.S2114PastedTwoCell f g T ptA Pg m)
    (p := (S2114ProbeChosenBase.S2114D f g T ptA Pg).toX1)
    (q := (S2114ProbeChosenBase.S2114D f g T ptA Pg).square1.toY)
    (x := (S2114ProbeChosenBase.S2114D f g T ptA Pg).x1)
    (z := (S2114ProbeChosenBase.S2114D f g T ptA Pg).xi)
    (c1 := (S2114ProbeChosenBase.S2114D f g T ptA Pg).c1)
    (nn := m.toX) (mq := m.toY)
    (a_s := S2107ExtLiftToX (S2114ProbeChosenBase.S2114D f g T ptA Pg)
      (S2114ProbeChosenBase.S2114WP f g T ptA Pg) s)
    (a_t := S2107ExtLiftToX (S2114ProbeChosenBase.S2114D f g T ptA Pg)
      (S2114ProbeChosenBase.S2114WP f g T ptA Pg) t)
    (c_s := s.commutes) (c_t := t.commutes)
    (S2114ProbeChosenBase.S2114PastedTwoCell_toX f g T ptA Pg m) m.compatibility

end LeanFormal.IUT.XiFPaper.S2114ProbeChosen
end
