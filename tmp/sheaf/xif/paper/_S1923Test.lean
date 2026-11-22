import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign

open Polynomial
open scoped Polynomial.Bivariate

universe u
namespace S1923Test
open IsEllipticNet

variable {R : Type u} [CommRing R] (W : ℤ → R)

example : (1:ℤ)+1=2 := by grind
example (a b c d : ℤ) : [a,b,c,d].Pairwise (· % 2 = · % 2) → a % 2 = b % 2 := by
  intro h; exact (List.pairwise_cons.mp h).1 a (by simp)
example (t : Fin 4 → ℤ) : Antitone (t ∘ (Fin.revPerm.trans (Tuple.sort t))) := by
  intro i j hij
  exact (Tuple.monotone_sort t) (Fin.rev_le_rev.mpr hij)

end S1923Test
