/- O6 P3: terminal normal form facts: an irreducible polynomial of degree at most one over
`ℚ` has degree exactly one (the input to the finite-beta base case of the general branch
pinning). REUSE:
- `Mzk1G1O6M2PinRecursionActual.natDegree_le_one_of_terminal` (this lane),
- `Irreducible.natDegree_pos` (Mathlib).
Root extraction from a linear irreducible polynomial is the next step (with alan's
`Mzk1G1O6M2PinTerminalActual.terminal_finset_rat`).
DEDUP: no such terminal-degree lemma existed in the tree. -/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinRecursionActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinTerminalBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinRecursionActual

/-- An irreducible polynomial of degree at most one over `ℚ` has degree exactly one:
degree zero would make it a unit. -/
theorem natDegree_eq_one_of_irreducible_of_le_one {p : ℚ[X]} (hp : Irreducible p)
    (hdeg : p.natDegree ≤ 1) : p.natDegree = 1 :=
  le_antisymm hdeg hp.natDegree_pos

/-- Every member of a terminal normal form has degree exactly one. -/
theorem natDegree_eq_one_of_mem_terminal {P : Finset ℚ[X]} (hP : pinMaxDeg P < 2)
    {p : ℚ[X]} (hp : p ∈ P) (hirr : Irreducible p) : p.natDegree = 1 :=
  natDegree_eq_one_of_irreducible_of_le_one hirr (natDegree_le_one_of_terminal hP hp)

#print axioms natDegree_eq_one_of_irreducible_of_le_one
#print axioms natDegree_eq_one_of_mem_terminal
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinTerminalBridgeActual
