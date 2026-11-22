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

noncomputable def cancel :
    (Ω ⊗[R] X) ⊗[X] Y ≃ₗ[R] Ω ⊗[R] Y :=
  (TensorProduct.congr (R := X)
      (Algebra.TensorProduct.commRight R X Ω).symm.toLinearEquiv (LinearEquiv.refl X Y)).restrictScalars R ≪≫ₗ
    (TensorProduct.comm X (X ⊗[R] Ω) Y).restrictScalars R ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R X X Y Ω).restrictScalars R ≪≫ₗ
    (TensorProduct.comm R Y Ω)

example (ω : Ω) (x : X) (y : Y) :
    cancel (R := R) (Ω := Ω) (X := X) (Y := Y) ((ω ⊗ₜ[R] x) ⊗ₜ[X] y) =
      ω ⊗ₜ[R] (x • y) := by
  simp [cancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

end

end S1842Probe
