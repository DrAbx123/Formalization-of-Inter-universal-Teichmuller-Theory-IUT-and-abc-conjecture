import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerInjectivity
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1WQMembershipTransferActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalIntegralUnitKummerInjectivity
open scoped Valued

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem normedInteger_mem_valuativeInteger {x : ℚ_[5]}
    (hx : x ∈ (NormedField.valuation (K := ℚ_[5])).integer) :
    x ∈ (ValuativeRel.valuation ℚ_[5]).integer := by
  rw [Valuation.mem_integer_iff]
  apply ((ValuativeRel.valuation ℚ_[5]).vle_one_iff).mp
  apply ((Padic.mulValuation (p := 5)).vle_one_iff).mpr
  have hnorm : ‖x‖ ≤ 1 := (mem_integers_iff x).mp hx
  exact (padicMulValuation_le_one_iff_norm_le_one 5 x).mpr hnorm



theorem valuativeInteger_mem_normedInteger {x : ℚ_[5]}
    (hx : x ∈ (ValuativeRel.valuation ℚ_[5]).integer) :
    x ∈ (NormedField.valuation (K := ℚ_[5])).integer := by
  rw [mem_integers_iff]
  apply (padicMulValuation_le_one_iff_norm_le_one 5 x).mp
  apply ((Padic.mulValuation (p := 5)).vle_one_iff).mp
  exact ((ValuativeRel.valuation ℚ_[5]).vle_one_iff).mpr
    (((ValuativeRel.valuation ℚ_[5]).mem_integer_iff x).mp hx)

#print axioms valuativeInteger_mem_normedInteger


noncomputable def normedIntegerEquivValuative :
    (NormedField.valuation (K := ℚ_[5])).integer ≃+*
      (ValuativeRel.valuation ℚ_[5]).integer where
  toFun x := ⟨x, normedInteger_mem_valuativeInteger x.property⟩
  invFun x := ⟨x, valuativeInteger_mem_normedInteger x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl


noncomputable def padicIntegersEquivZp :
    (NormedField.valuation (K := ℚ_[5])).integer ≃+* ℤ_[5] :=
  (normedIntegerEquivValuative).trans
    (LeanFormal.IUT.LocalIntegralUnitKummerInjectivity.padicCanonicalIntegerEquiv 5)



#print axioms padicIntegersEquivZp

#print axioms normedIntegerEquivValuative

#print axioms normedInteger_mem_valuativeInteger
end LeanFormal.IUT.XiFPaper.Mzk1WQMembershipTransferActual