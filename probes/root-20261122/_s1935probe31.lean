import tmp.sheaf.xif.paper.S1935CatCoherenceActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

set_option pp.universes true in
#check S1726K
set_option pp.universes true in
#check (SchemeOverField S1726K)
set_option pp.universes true in
#check LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ
set_option pp.universes true in
#check (fun (A : S1728Cover) => A.source.fiber)

end
