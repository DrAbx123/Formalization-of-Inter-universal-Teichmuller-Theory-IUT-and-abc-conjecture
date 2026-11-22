import tmp.sheaf.xif.paper.S2240StrictConeIsoActual
import tmp.sheaf.xif.paper.S2350D6AfterRefuteActual
import tmp.sheaf.xif.paper.S2086ToAAssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
namespace LeanFormal.IUT.XiFPaper.S2357CorrectedD6ApexActual

theorem S2357UniformApexImpossible : S2130ConcreteTwoPullback -> False :=
  S2350NotConcreteTwoPullback

theorem S2357NoUniformApex : Not (Nonempty S2130ConcreteTwoPullback) :=
  S2350NotNonemptyConcreteTwoPullback

def S2357PerCoverCoherenceRequired (B C : S1728Cover) : Prop :=
  S2240ConeEssSurjAt B C

theorem S2357StrongCoverCoherence (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) :
    S2357PerCoverCoherenceRequired B (StrongCover.cover Cs) :=
  S2240ConeEssSurjAt_of_strongCover Cs B

noncomputable def S2357StrongCoverPresentation
    (Cs : StrongCover S1726Orbicurve) (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) :=
  S2240HgFor_strongCover Cs B A f g T ptA

theorem S2357StrongCoverPresentation_finiteEtale
    (Cs : StrongCover S1726Orbicurve) (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    And (IsFinite ((S2357StrongCoverPresentation Cs B A f g T ptA).projection.left))
      (Etale ((S2357StrongCoverPresentation Cs B A f g T ptA).projection.left)) :=
  S2240HgFor_strongCover_finiteEtale Cs B A f g T ptA

def S2357CorrectedD6FirstMissing : Prop :=
  forall (B C : S1728Cover), S2240ConeEssSurjAt B C

end LeanFormal.IUT.XiFPaper.S2357CorrectedD6ApexActual
end