import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
namespace Test
theorem signGroup_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod 2, g = Multiplicative.ofAdd a :=
    ⟨g.toAdd, (ofAdd_toAdd g).symm⟩
  fin_cases a <;> simp
end Test
