import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

noncomputable section
set_option maxHeartbeats 2000000
open scoped TensorProduct
open CategoryTheory

namespace S1842Probe

section
variable {R Ω X Y : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
  [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] [Algebra X Y] [IsScalarTower R X Y]

local instance : Algebra X (Ω ⊗[R] X) := Algebra.TensorProduct.rightAlgebra
local instance : Algebra X (X ⊗[R] Ω) := Algebra.TensorProduct.leftAlgebra

example : (Ω ⊗[R] X) ≃ₐ[X] (X ⊗[R] Ω) :=
  (Algebra.TensorProduct.commRight R X Ω).symm

example (x : X) (ω : Ω) (x' : X) :
    (Algebra.TensorProduct.commRight R X Ω).symm (ω ⊗ₜ[R] x') = x' ⊗ₜ[R] ω := by
  simp [Algebra.TensorProduct.commRight]

end

end S1842Probe
