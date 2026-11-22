import tmp.sheaf.xif.paper.S1865CoprodApexActual

noncomputable section
open CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1871CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1865CoprodApexActual

example (h : S1878EssSurj) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory01 :=
  S1865Coherent01HasFiniteCoproducts h

example (h : S1878EssSurj) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 :=
  S1865Coherent11HasFiniteCoproducts h

example (h : S1878EssSurj) (hE : S1871EssSurj) :
    S1833FirstMissing :=
  S1865S1833FirstMissing h hE

example (hE : S1871EssSurj) : S1865EssentialCoproductApex :=
  S1865EssentialCoproductApex_of_essSurj hE

#print axioms S1865Coherent01HasFiniteCoproducts
#print axioms S1865S1833FirstMissing
#print axioms S1865EssentialCoproductApex_of_essSurj

end