import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
open scoped TensorProduct
example (k R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [CommRing k] [Algebra R k]
    [Module.Finite R A] : Module.Finite k (k ⊗[R] A) := inferInstance
