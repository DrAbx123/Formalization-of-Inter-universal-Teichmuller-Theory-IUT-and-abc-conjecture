import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
namespace Test
theorem signGroup_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, g = Multiplicative.ofAdd a :=
    ⟨g.toAdd, (ofAdd_toAdd g).symm⟩
  rw [ha]
  fin_cases a
  · left; rfl
  · right; rfl
end Test
