/- O6 P3: recursion assembly for the general branch pinning (route §4.3): by well-founded
induction along the lexicographic measure, the Belyi degree reduction iterates to a terminal
set of irreducible polynomials of degree < 2. REUSE:
- `Mzk1G1O6M2PinGeneralActual.pinLt` / `Mzk1G1O6M2PinStepActual.pinReductionStep_holds`,
- `Mzk1G1O6M2PinComposeActual.wellFounded_pinLt` (termination, this lane).
The value-pinning of the terminal (affine) stage uses alan's P2 interface
(`Mzk1G1O6M2PinValueActual.pinValue_avoid`) — next batch.
DEDUP: no existing recursion assembly in the tree. -/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinComposeActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinRecursionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinStepActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinComposeActual

/-- **Terminal normal form**: iterating the Belyi degree reduction along the well-founded
lexicographic measure reaches a finite set of irreducible polynomials of degree at most one.
-/
theorem exists_terminal (P : Finset ℚ[X]) (hP : ∀ p ∈ P, Irreducible p) :
    ∃ P' : Finset ℚ[X], (∀ p ∈ P', Irreducible p) ∧ pinMaxDeg P' < 2 := by
  let C : Finset ℚ[X] → Prop := fun Q => (∀ p ∈ Q, Irreducible p) →
    ∃ P' : Finset ℚ[X], (∀ p ∈ P', Irreducible p) ∧ pinMaxDeg P' < 2
  have h : ∀ Q, (∀ R, pinLt R Q → C R) → C Q := by
    intro Q ih hQ
    by_cases h2 : 2 ≤ pinMaxDeg Q
    · obtain ⟨Q', hQ'irr, hlt⟩ := pinReductionStep_holds Q hQ h2
      exact ih Q' hlt hQ'irr
    · exact ⟨Q, hQ, by omega⟩
  exact wellFounded_pinLt.induction P h hP

/-- Every member of a terminal set has degree at most one. -/
theorem natDegree_le_one_of_terminal {P : Finset ℚ[X]} (hP : pinMaxDeg P < 2)
    {p : ℚ[X]} (hp : p ∈ P) : p.natDegree ≤ 1 := by
  have h1 : p.natDegree ≤ pinMaxDeg P := pinMaxDeg_le hp
  omega

#print axioms exists_terminal
#print axioms natDegree_le_one_of_terminal
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinRecursionActual