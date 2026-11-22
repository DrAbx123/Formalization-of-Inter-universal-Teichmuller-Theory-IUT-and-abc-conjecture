import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable def test_e : FinitePadicTensor (p := 5) (fun _ : Unit => ℚ_[5]) ≃ₗ[ℚ_[5]] ℚ_[5] :=
  PiTensorProduct.subsingletonEquiv (i₀ := ())
