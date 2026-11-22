import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
open LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section
letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
noncomputable def test_e : FinitePadicTensor (p := 5) (fun _ : Unit => ℚ_[5]) ≃ₗ[ℚ_[5]] ℚ_[5] :=
  (PiTensorProduct.subsingletonEquiv (R := ℚ_[5]) (i₀ := ()) : (PiTensorProduct ℚ_[5] (fun _ : Unit => ℚ_[5])) ≃ₗ[ℚ_[5]] ℚ_[5])
end
