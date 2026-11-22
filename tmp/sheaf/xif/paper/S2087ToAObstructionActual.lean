import tmp.sheaf.xif.paper.S2086ToAAssemblyActual

/-! # S2087: why S2086WitnessBaseChangeStatement needs g.map finite etale

To construct the cone over the iso-comma square from a point `ptA` of A,
one needs a point of `B.source.fiber` over the *C.source* point
`ptA ≫ f.map`.  The only finite-etale presentation available in the tree is
`B.finiteEtale : EtaleStackFiniteEtaleMorphism B.map`, whose target is the
orbicurve stack `S1726Orbicurve.stack`, not `C.source.fiber`.

Thus the exact additional input is a finite-etale certificate for
`g.map : B.source.Hom C.source` (equivalently, a direct finite-etale proof
for `structureMap = toA ≫ A.map`).  No such certificate is asserted here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual

universe u

/-- Exact additional input needed for the ToA cone construction: every cover
map `g : B -> C` is itself representably finite etale. -/
def S2087GMapFiniteEtaleField : Type 1 :=
  ∀ (A B C : S1728Cover) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism g.map

/-- The same input, specialized to the second leg of a cospan. -/
def S2087CospanGMapFiniteEtaleField : Type 1 :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism g.map

#check S2087GMapFiniteEtaleField
#check S2087CospanGMapFiniteEtaleField

end LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual

end
