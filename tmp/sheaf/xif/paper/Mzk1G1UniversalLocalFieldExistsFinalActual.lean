/- Route 7.2 final consumer: unconditional names for the conditional universal-local-field
statement, for henry's GKCompactInput lane and andrew's P8 lane. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalHgenInterfaceActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLocalFieldExistsFinalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalHgenInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual

variable {p : Nat} [Fact p.Prime]

/-- Final name: residue-root generation for some modulus gives the universal local field. -/
theorem universalLocalFieldExists_final (d : Nat)
    (h : ∃ N : Nat, ResidueRootGeneration (p := p) d N) :
    UniversalLocalFieldExists (p := p) d :=
  universalLocalFieldExists_of_residueRootGeneration (p := p) d h

/-- Final name: bounded-degree finiteness from residue-root generation. -/
theorem boundedDegreeFinitelyManyFields_final (d N : Nat)
    (h : ResidueRootGeneration (p := p) d N) :
    BoundedDegreeFinitelyManyFields (p := p) d :=
  boundedDegreeFinitelyManyFields_of_residueRootGeneration (p := p) d N h

#print axioms universalLocalFieldExists_final
#print axioms boundedDegreeFinitelyManyFields_final
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLocalFieldExistsFinalActual
