import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

section
variable {A C : S1728Cover} (f : S1728CoverMap A C)

#check f.map
#check (f.map : Pseudofunctor.StrongTrans A.source.fiber C.source.fiber)
example : (f.map : Pseudofunctor.StrongTrans A.source.fiber C.source.fiber) = f.map := rfl

#check @natCompHomApp (LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) _ A.source.fiber C.source.fiber

end

end
