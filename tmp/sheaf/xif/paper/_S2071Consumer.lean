import tmp.sheaf.xif.paper.S2071PastingWitnessActual

noncomputable section

open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

#check @S2071PastingStatement_holds
#print axioms S2071PastingStatement_holds
#print axioms S2071S2044CompositionClosure

/-- D6(c): the S2043 finite-etale certificate now needs only the toA input. -/
noncomputable def S2071D6CertificateOfToA (htoA : S2044ToAFiniteEtaleField)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2058D6FiniteEtaleCertificate S2071PastingStatement_holds htoA f g

#print axioms S2071D6CertificateOfToA

end
