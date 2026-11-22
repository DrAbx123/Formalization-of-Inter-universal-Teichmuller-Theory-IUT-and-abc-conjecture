import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps

open CategoryTheory
open scoped TensorProduct
open Finset

universe u

namespace S1747Probe

lemma idem_eq_zero_or_one {L : Type} [Field L] {x : L} (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp (show x * (1 - x) = 0 by
    rw [mul_sub, mul_one, hx.eq, sub_self]) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

example {J : Type} [Finite J] (Bj : J → Type) [∀ j, CommRing (Bj j)]
    [∀ j, Algebra K (Bj j)] [∀ j, Field (Bj j)] : Algebra K (∀ j, Bj j) := inferInstance

end S1747Probe
