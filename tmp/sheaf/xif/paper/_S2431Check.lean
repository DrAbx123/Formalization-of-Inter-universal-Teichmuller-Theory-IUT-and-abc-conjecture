import tmp.sheaf.xif.paper.S2431CompositeMapIsoActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2424CoverCompositionActual
open LeanFormal.IUT.XiFPaper.S2429CompositeAssemblyActual
open LeanFormal.IUT.XiFPaper.S2431CompositeMapIsoActual

#check S2431CompositeMapIsoRequired_holds
#print axioms S2431CompositeMapIsoRequired_holds
#print axioms S2431HomOfStrongTrans_vcomp
#print axioms S2431CastHomMidIso

/-- Target lock: the theorem has exactly the required statement. -/
example {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) : S2429CompositeMapIsoRequired H :=
  S2431CompositeMapIsoRequired_holds H

end
end