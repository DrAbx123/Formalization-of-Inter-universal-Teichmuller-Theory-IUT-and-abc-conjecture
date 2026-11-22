/- Route 7.2 output for G-K: expand UniversalLocalFieldExists into its L and
ContainsBoundedExtensions components, given the residue-root generation input. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalLocalFieldExistsFinalActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalContainsBoundedActual

open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLocalFieldExistsFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalHgenInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual

variable {p : Nat} [Fact p.Prime]

/-- Given residue-root generation, the universal local field provides an actual field L
containing all degree <= d extensions (the G-K local field L_v). -/
theorem exists_containsBoundedExtensions_of_hgen (d : Nat)
    (h : ∃ N : Nat, ResidueRootGeneration (p := p) d N) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (Padic p) L)
      (_ : FiniteDimensional (Padic p) L) (_ : Normal (Padic p) L),
      ContainsBoundedExtensions p d L := by
  have hU : UniversalLocalFieldExists (p := p) d :=
    universalLocalFieldExists_final (p := p) d h
  simpa [UniversalLocalFieldExists] using hU

#print axioms exists_containsBoundedExtensions_of_hgen
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalContainsBoundedActual
