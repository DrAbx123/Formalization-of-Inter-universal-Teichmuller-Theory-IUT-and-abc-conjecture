import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1InfiniteDivisibleActual

universe uG
variable {G : Type uG} [CommGroup G]

/-- An element is infinitely divisible in degree `r` if it has `r^n`-th roots
for every `n`. -/
def InfinitelyDivisibleFor (r : Nat) (x : G) : Prop :=
  ∀ n : Nat, ∃ y : G, y ^ (r ^ n) = x

theorem infinitelyDivisibleFor_one (r : Nat) :
    InfinitelyDivisibleFor r (1 : G) := by
  intro n
  exact ⟨1, by simp⟩

/-- The subgroup of elements infinitely divisible in degree `r`. -/
def infinitelyDivisibleSubgroup (r : Nat) : Subgroup G where
  carrier := {x | InfinitelyDivisibleFor r x}
  one_mem' := infinitelyDivisibleFor_one r
  mul_mem' := by
    intro x y hx hy n
    obtain ⟨a, ha⟩ := hx n
    obtain ⟨b, hb⟩ := hy n
    refine ⟨a * b, ?_⟩
    rw [mul_pow, ha, hb]
  inv_mem' := by
    intro x hx n
    obtain ⟨a, ha⟩ := hx n
    refine ⟨a⁻¹, ?_⟩
    rw [inv_pow, ha]

theorem mem_infinitelyDivisibleSubgroup (r : Nat) (x : G) :
    x ∈ infinitelyDivisibleSubgroup r ↔ InfinitelyDivisibleFor r x :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ind1InfiniteDivisibleActual