import tmp.sheaf.xif.paper.S2076IsoCommaTwoPullbackActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual

universe u
variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

#check S1893LiftIsoOfConeIso
#check S1893ComparisonFunctor
#check gLiftApp
#check gConeAt
#check gLiftSite
#check Pseudofunctor.StrongTrans.isoMk
#check S1836IsoComma_hom_ext
#check S1893Cone.Hom
