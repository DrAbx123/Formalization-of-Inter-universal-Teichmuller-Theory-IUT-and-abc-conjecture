import tmp.sheaf.xif.paper.S2001LiftCommutesActual

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual

namespace S2001ConsumerCheck

example {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (W : S1728Cover) (c : S1832Bicone f g W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (liftSite (f := f) (g := g) c)
      (structureMap f g)) W.map :=
  liftCommutes f g W c

#check liftCommutes
#check S2001CoverFiberDiscrete
#check S2001UniqFirstMissing

end S2001ConsumerCheck
