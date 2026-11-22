/- Route 7.2: combine the explicit N(d) with the residue-root generation assembly,
reducing UniversalLocalFieldExists to the single analytic input SeparationInput. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalNExplicitActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalResidueRootGenerationActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalLocalFieldExistsFinalActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationToUFLEActual

open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalNExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResidueRootGenerationActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLocalFieldExistsFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalHgenInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual

variable {p : Nat} [Fact p.Prime]

/-- Explicit N(d) plus the assembly: SeparationInput gives residue-root generation. -/
theorem exists_residueRootGeneration_of_separationInput (d B : Nat)
    (hsep : SeparationInput (p := p) d B) :
    ∃ N : Nat, ResidueRootGeneration (p := p) d N := by
  obtain ⟨N, hNpos, hsmall⟩ := exists_residueModulus (p := p) d B
  exact ⟨N, residueRootGeneration_of_separationInput d B N hNpos hsmall hsep⟩

/-- The universal local field exists once SeparationInput is available. -/
theorem universalLocalFieldExists_of_separationInput (d B : Nat)
    (hsep : SeparationInput (p := p) d B) :
    UniversalLocalFieldExists (p := p) d :=
  universalLocalFieldExists_final (p := p) d (exists_residueRootGeneration_of_separationInput d B hsep)

#print axioms exists_residueRootGeneration_of_separationInput
#print axioms universalLocalFieldExists_of_separationInput
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationToUFLEActual
