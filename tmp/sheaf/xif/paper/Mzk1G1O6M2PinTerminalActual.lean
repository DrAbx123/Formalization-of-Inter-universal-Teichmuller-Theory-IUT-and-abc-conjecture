/- O6 / M2 terminal-set base case interface for henry's P3.

Reuse: Mathlib minpoly.natDegree_eq_one_iff / minpoly.natDegree_pos.
-/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinValueActual
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinTerminalActual

/-- A terminal value (minpoly degree <= 1) is rational. -/
theorem exists_rat_of_natDegree_minpoly_le_one {x : ℂ} (hx : IsAlgebraic ℚ x)
    (h : (minpoly ℚ x).natDegree ≤ 1) :
    ∃ q : ℚ, algebraMap ℚ ℂ q = x := by
  have hpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hx.isIntegral
  have h1 : (minpoly ℚ x).natDegree = 1 := le_antisymm h hpos
  rcases (minpoly.natDegree_eq_one_iff (A := ℚ) (B := ℂ)).mp h1 with ⟨q, hq⟩
  exact ⟨q, hq⟩

/-- A finite terminal set consists of rational values. -/
theorem terminal_finset_rat {S : Finset ℂ}
    (hS : ∀ x ∈ S, IsAlgebraic ℚ x) (hdeg : ∀ x ∈ S, (minpoly ℚ x).natDegree ≤ 1) :
    ∃ T : Finset ℚ, ∀ x ∈ S, ∃ q ∈ T, algebraMap ℚ ℂ q = x := by
  classical
  let f : ℂ → ℚ := fun x => if hx : ∃ q : ℚ, algebraMap ℚ ℂ q = x then Classical.choose hx else 0
  refine ⟨S.image f, ?_⟩
  intro x hxmem
  obtain ⟨q, hq⟩ := exists_rat_of_natDegree_minpoly_le_one (hS x hxmem) (hdeg x hxmem)
  refine ⟨q, Finset.mem_image.mpr ⟨x, hxmem, ?_⟩, hq⟩
  -- f x = q because the chosen witness is unique
  dsimp [f]
  rw [dif_pos ⟨q, hq⟩]
  exact (Classical.choose_spec ⟨q, hq⟩).symm ▸ rfl

#print axioms exists_rat_of_natDegree_minpoly_le_one
#print axioms terminal_finset_rat
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinTerminalActual
