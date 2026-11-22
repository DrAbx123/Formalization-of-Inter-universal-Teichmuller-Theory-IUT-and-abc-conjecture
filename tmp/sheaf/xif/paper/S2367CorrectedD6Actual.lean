import tmp.sheaf.xif.paper.S2357CorrectedD6ApexActual
import tmp.sheaf.xif.paper.S2359S2086DirectActual

noncomputable section
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual
open LeanFormal.IUT.XiFPaper.S2350D6AfterRefuteActual
open LeanFormal.IUT.XiFPaper.S2357CorrectedD6ApexActual
open LeanFormal.IUT.XiFPaper.S2359S2086DirectActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
namespace LeanFormal.IUT.XiFPaper.S2367CorrectedD6Actual

abbrev S2367CorrectedApex
    {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) : Type _ :=
  EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA)


noncomputable def S2367CorrectedApexOfStrongCover
    (Cs : StrongCover S1726Orbicurve) (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    S2367CorrectedApex f g T ptA :=
  S2357StrongCoverPresentation Cs B A f g T ptA

theorem S2367CorrectedApexOfStrongCover_finiteEtale
    (Cs : StrongCover S1726Orbicurve) (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    And (IsFinite ((S2367CorrectedApexOfStrongCover Cs B A f g T ptA).projection.left))
      (Etale ((S2367CorrectedApexOfStrongCover Cs B A f g T ptA).projection.left)) :=
  S2357StrongCoverPresentation_finiteEtale Cs B A f g T ptA

abbrev S2367DirectFirstMissing : Type 1 :=
  S2086StackCancellation

noncomputable def S2367S2086CospanGMapFiniteEtaleOfCancellation
    (hc : S2367DirectFirstMissing) :
    S2086CospanGMapFiniteEtale :=
  S2359S2086CospanGMapFiniteEtaleOfCancellation hc



theorem S2367S2291Presentation :
    Nonempty (EtaleStackBaseChangePresentation
      (LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual.S2291F).map
      LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual.S2291T
      (LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual.S2130PtC
        LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual.S2291F
        LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual.S2291T
        LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual.S2291PtA)) :=
  LeanFormal.IUT.XiFPaper.S2350D6AfterRefuteActual.S2350PresentationAtDatum

#check S2350PresentationAtDatum

end LeanFormal.IUT.XiFPaper.S2367CorrectedD6Actual
end