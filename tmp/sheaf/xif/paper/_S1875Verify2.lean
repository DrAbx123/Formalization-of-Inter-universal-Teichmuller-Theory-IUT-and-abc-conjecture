import tmp.sheaf.xif.paper.S1875CoherentGaloisAssemblyActual

noncomputable section
open CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1875CoherentGaloisAssemblyActual
open LeanFormal.IUT.XiFPaper.S1868CoherentFiberActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual

attribute [local instance] S1854CoherentCategory01

set_option pp.all true in
#check S1875GaloisCategory_of_essSurj

example (h : S1868EssSurj) (hIso : S1835BCReflectsIsos) :
    GaloisCategory CoherentCover :=
  S1875GaloisCategory_of_essSurj h hIso

example (h : S1868EssSurj) (hIso : S1835BCReflectsIsos) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1875GaloisCategory_of_essSurj h hIso
