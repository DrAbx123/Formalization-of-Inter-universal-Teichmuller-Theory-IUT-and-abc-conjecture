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

theorem cancel_tmul_one (m : Ω ⊗[R] X) :
    cancel (R := R) (Ω := Ω) (X := X) (Y := Y) (m ⊗ₜ[X] (1 : Y)) =
      Algebra.TensorProduct.map (AlgHom.id R Ω) (IsScalarTower.toAlgHom R X Y) m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add m n hm hn =>
    rw [TensorProduct.add_tmul, map_add, hm, hn, map_add]
  | tmul ω x =>
    simp [cancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]

theorem eq_zero_of_map_eq_zero [Module.FaithfullyFlat X Y] (m : Ω ⊗[R] X)
    (hm : Algebra.TensorProduct.map (AlgHom.id R Ω) (IsScalarTower.toAlgHom R X Y) m = 0) :
    m = 0 := by
  have h0 : cancel (R := R) (Ω := Ω) (X := X) (Y := Y) (m ⊗ₜ[X] (1 : Y)) = 0 := by
    rw [cancel_tmul_one, hm]
  have h1 : m ⊗ₜ[X] (1 : Y) = 0 := by
    have := congrArg (cancel (R := R) (Ω := Ω) (X := X) (Y := Y)).symm h0
    simpa using this
  have h2 : (1 : Y) ⊗ₜ[X] m = 0 := by
    have := congrArg (TensorProduct.comm X (Ω ⊗[R] X) Y) h1
    simpa using this
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := X) (B := Y) (M := Ω ⊗[R] X)
    (by simpa using h2)

theorem injective_of_faithfullyFlat [Module.FaithfullyFlat X Y] :
    Function.Injective (fun m : Ω ⊗[R] X =>
      Algebra.TensorProduct.map (AlgHom.id R Ω) (IsScalarTower.toAlgHom R X Y) m) := by
  intro m n hmn
  have hsub : (Algebra.TensorProduct.map (AlgHom.id R Ω) (IsScalarTower.toAlgHom R X Y)) (m - n) = 0 := by
    rw [map_sub, sub_eq_zero.mpr hmn]
  have hzero : m - n = 0 := eq_zero_of_map_eq_zero (R := R) (Ω := Ω) (X := X) (Y := Y) (m - n) hsub
  exact sub_eq_zero.mp hzero

end

end S1842Probe
