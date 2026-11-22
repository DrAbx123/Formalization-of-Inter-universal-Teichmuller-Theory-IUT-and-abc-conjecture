/- Route 7.2 exports for downstream lanes (henry GK/GKCompactInput, andrew P8):
the exact names of the conditional bounded-degree finiteness and universal local field results. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalHgenInterfaceActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalUnramifiedCaseActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalMonogenicExistenceActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalExportActual

open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalHgenInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual

variable {p : Nat} [Fact p.Prime]

/-- Export: residue-root generation gives bounded-degree finiteness. -/
theorem boundedDegreeFinitelyManyFields_export (d N : Nat)
    (h : ResidueRootGeneration (p := p) d N) :
    BoundedDegreeFinitelyManyFields (p := p) d :=
  boundedDegreeFinitelyManyFields_of_residueRootGeneration (p := p) d N h

/-- Export: residue-root generation for some modulus gives the universal local field. -/
theorem universalLocalFieldExists_export (d : Nat)
    (h : ∃ N : Nat, ResidueRootGeneration (p := p) d N) :
    UniversalLocalFieldExists (p := p) d :=
  universalLocalFieldExists_of_residueRootGeneration (p := p) d h

#print axioms boundedDegreeFinitelyManyFields_export
#print axioms universalLocalFieldExists_export
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalExportActual
