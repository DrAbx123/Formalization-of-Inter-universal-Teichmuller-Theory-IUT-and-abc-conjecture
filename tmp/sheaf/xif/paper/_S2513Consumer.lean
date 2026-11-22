import tmp.sheaf.xif.paper.S2513SeparationUB

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2511InfinityPointUB
open LeanFormal.IUT.XiFPaper.S2513SeparationUB

/-- Frozen target, checked against the exported olean. -/
example : ∀ s : S2508ResidueScheme ⟶ S2508AffineOver,
    s ≫ S2508ChartOverMap ≠ S2511Point := S2513Separation

#check @S2513Separation
#print axioms S2513Separation
#print axioms S2513CuspDatumOf

end
