import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual
open CategoryTheory
open CategoryTheory.Bicategory
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
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
namespace Probe
variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
variable {W : S1728Cover} (c : S1832Bicone f g W)
#check c.commutes
#check c.commutes.hom
#check c.commutes.hom.as
#check c.commutes.hom.as.app
#check c.commutes.inv.as.app
#check Pseudofunctor.StrongTrans.Modification
#check Pseudofunctor.StrongTrans.isoMk
#check S1893Cone
#check S1893ComparisonFunctor
#check S1893Lift
#check S1893LiftUniq
end Probe
