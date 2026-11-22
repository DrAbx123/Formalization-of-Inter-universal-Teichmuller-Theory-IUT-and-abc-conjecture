import tmp.sheaf.xif.paper.S2028SourceSchemeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2028Consumer

open LeanFormal.IUT.XiFPaper.S2028SourceSchemeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2018IdentityRepairActual
open LeanFormal.IUT.XiFPaper.S2015FullPullbackActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
open LeanFormal.IUT.XiFPaper.S2023SourceSchemeActual

example : S2018SourceSchemeAll := S2028SourceSchemeAll
example : S2023FirstMissing := S2028S2023FirstMissing
example : S2015IdentityRepairAll := S2028IdentityRepairAll
example : S2018FirstMissing := S2028FirstMissing
example : S2001UniqFirstMissing := S2028UniqFirstMissing
example (A : S1728Cover) : S2018SourceScheme A := S2028SourceScheme A
example (A : S1728Cover) : S2015IdentityRepair A := S2028IdentityRepair A

#print axioms S2028SourceSchemeAll
#print axioms S2028S2023FirstMissing
#print axioms S2028IdentityRepairAll
#print axioms S2028FirstMissing
#print axioms S2028UniqFirstMissing

end LeanFormal.IUT.XiFPaper.S2028Consumer
