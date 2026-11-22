import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic

open CategoryTheory
open scoped TensorProduct
open Finset

universe u

namespace S1747Probe

example {I J L : Type} (Bj : J → Type) [∀ j, CommRing (Bj j)] {K : Type} [Field K]
    [∀ j, Algebra K (Bj j)] [Field L] [Algebra K L]
    (f : I → J) (σ : ∀ i, Bj (f i) →ₐ[K] L) :
    True := by
  have test : ∀ i1 i2, f i1 = f i2 → Bj (f i1) →ₐ[K] L := by
    intro i1 i2 h12
    have σ2' : Bj (f i1) →ₐ[K] L := h12 ▸ σ i2
    exact σ2'
  trivial

end S1747Probe
