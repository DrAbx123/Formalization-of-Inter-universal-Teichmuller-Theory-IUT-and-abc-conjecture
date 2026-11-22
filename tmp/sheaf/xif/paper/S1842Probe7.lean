import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

noncomputable section
set_option maxHeartbeats 1000000
open scoped TensorProduct
open CategoryTheory

namespace S1842Probe

section
variable {R Ω X Y : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
  [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] [Algebra X Y] [IsScalarTower R X Y]

-- X-module structure on Ω ⊗[R] X via the right factor.
local instance : Algebra X (Ω ⊗[R] X) := Algebra.TensorProduct.rightAlgebra

example : Module X (Ω ⊗[R] X) := inferInstance
example : Module X Y := Algebra.toModule

-- fixed y, map X → Y, x ↦ x • y
def lmulY (y : Y) : X →ₗ[R] Y where
  toFun x := x • y
  map_add' x x' := by simp [add_smul]
  map_smul' r x := by simp [smul_assoc]

example (m : Ω ⊗[R] X) (y : Y) : Ω ⊗[R] Y :=
  TensorProduct.map (LinearMap.id : Ω →ₗ[R] Ω) (lmulY (R := R) (X := X) (Y := Y) y) m

end

end S1842Probe
