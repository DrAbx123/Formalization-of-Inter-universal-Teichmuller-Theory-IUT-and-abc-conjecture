import tmp.sheaf.xif.paper.Mzk1LatticeOrbitIndexActual
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula

/-! A2 bridge: latticeIndex (Submodule form) = Nat.card of the module quotient. -/
noncomputable section
open Module
namespace LeanFormal.IUT.XiFPaper.Mzk1IndexCardBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual
variable {p : Nat} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (PadicInt p) E]
variable (M : Submodule (PadicInt p) E)
/-- The A2 index of `N.map M.subtype ≤ M` equals `#(M/N)`. -/
theorem latticeIndex_toAddSubgroup_eq_natCard_quotient
    (N : Submodule (PadicInt p) M) :
    latticeIndex ((N.map M.subtype).toAddSubgroup) (M.toAddSubgroup) = Nat.card (M ⧸ N) := by
  rw [latticeIndex, LeanFormal.IUT.CompactOpenAddSubgroup.intersectionIndex,
    LeanFormal.IUT.CompactOpenAddSubgroup.intersectionInLeft]
  rw [Submodule.map_toAddSubgroup]
  change Nat.card (M.toAddSubgroup ⧸ AddSubgroup.comap (M.subtype : M →+ E)
    (AddSubgroup.map (M.subtype : M →+ E) N.toAddSubgroup)) = Nat.card (M ⧸ N)
  rw [AddSubgroup.comap_map_eq_self_of_injective (f := (M.subtype : M →+ E))
    (fun x y h => Subtype.ext h) N.toAddSubgroup]
  rfl
end LeanFormal.IUT.XiFPaper.Mzk1IndexCardBridgeActual
end