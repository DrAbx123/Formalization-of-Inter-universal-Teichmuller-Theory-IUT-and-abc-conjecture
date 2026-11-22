import tmp.sheaf.xif.paper.S1995PsiTildeLogTopFieldActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual
open LeanFormal.IUT.XiFPaper.S1974PsiTildeTopFieldActual
open LeanFormal.IUT.XiFPaper.S1995PsiTildeLogTopFieldActual

namespace S1995Consumer

#check @LeanFormal.IUT.XiFPaper.S1995PsiTildeLogTopFieldActual.psiTildeLogTopology_isTopologicalDivisionRing
#check @LeanFormal.IUT.XiFPaper.S1995PsiTildeLogTopFieldActual.paperR1Structure
#check @LeanFormal.IUT.XiFPaper.S1995PsiTildeLogTopFieldActual.r1FirstMissing_of_logTopology_eq_indTopology

example (v : FinitePrimePlace 2 7) : PaperR1Structure v := paperR1Structure v

end S1995Consumer
