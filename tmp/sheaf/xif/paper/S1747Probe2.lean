import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory
open scoped TensorProduct

universe u

namespace S1747Probe

variable {K : Type} [Field K]

example {L : Type} [Field L] {x : L} (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp (show x * (1 - x) = 0 by
    rw [mul_sub, mul_one, hx.eq, sub_self]) with h | h
  · left; exact h
  · right; exact (sub_eq_zero.mp h).symm

example (A : Type u) [CommRing A] [Algebra K A] (h : Algebra.Etale K A) :
    ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  (Algebra.Etale.iff_exists_algEquiv_prod K A).mp h

example {I : Type} [Finite I] (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    [∀ i, Algebra.Etale K (B i)] : Algebra.Etale K (∀ i, B i) := by
  infer_instance

example {I : Type} [Finite I] (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    [∀ i, Module.Finite K (B i)] : Module.Finite K (∀ i, B i) := by
  infer_instance

example {I : Type} [DecidableEq I] (i : I) (x y : ℚ) :
    Pi.single (M := fun _ => ℚ) i (x * y) =
      Pi.single (M := fun _ => ℚ) i x * Pi.single (M := fun _ => ℚ) i y := by
  ext j
  by_cases h : j = i <;> simp [h]

example {I : Type} [DecidableEq I] (i : I) (x : ℚ) :
    Pi.single (M := fun _ => ℚ) i x =
      Pi.single (M := fun _ => ℚ) i (1:ℚ) * Pi.single (M := fun _ => ℚ) i x := by
  ext j
  by_cases h : j = i <;> simp [h]

end S1747Probe
