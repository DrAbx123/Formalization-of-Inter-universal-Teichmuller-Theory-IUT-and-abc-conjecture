import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
namespace Test
theorem signGroup_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  have hg : g.toAdd = (0 : ZMod 2) ∨ g.toAdd = (1 : ZMod 2) := by
    fin_cases g.toAdd <;> simp
  rcases hg with h | h
  · left
    rw [← Multiplicative.ofAdd_toAdd g, h]
    rfl
  · right
    rw [← Multiplicative.ofAdd_toAdd g, h]
end Test
