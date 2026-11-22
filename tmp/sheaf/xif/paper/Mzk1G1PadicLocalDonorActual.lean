/- Ported donor from tmp/local-cft-port/PadicField/Ramification.lean:
   integersQpEquiv : 𝒪 p ℚ_[p] ≃+* ℤ_[p]
rewritten for the repository's Integers API (IntegralTraceDualTensorInclusion/IntegralUnits).
The base case of the local different/order conversion needs this identification. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PadicLocalDonorActual

open LeanFormal.IUT.LocalFieldIntegralUnits

variable {p : Nat} [Fact p.Prime]

/-- The valuation ring of Q_p is the p-adic integers (donor:
tmp/local-cft-port/PadicField/Ramification.lean, integersQpEquiv). -/
noncomputable def integersRatEquivPadicInt : Integers ℚ_[p] ≃+* ℤ_[p] where
  toFun x := ⟨(x : ℚ_[p]), x.property⟩
  invFun x := ⟨(x : ℚ_[p]), x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

#print axioms integersRatEquivPadicInt
end LeanFormal.IUT.XiFPaper.Mzk1G1PadicLocalDonorActual
