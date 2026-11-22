import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S2000CohomologicalPsiCnsActual
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitEvaluationImage

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2046M1LocalUnitsActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable def evaluatedUnitsEquivIntegersUnits :
    evaluatedUnitSubgroup p ≃* (Integers (AlgebraicClosure ℚ_[p]))ˣ where
  toFun u : (Integers (AlgebraicClosure ℚ_[p]))ˣ := {
    val := ⟨(u : (AlgebraicClosure ℚ_[p])ˣ), (mem_integers_iff _).mpr u.property.1⟩
    inv := ⟨((u : (AlgebraicClosure ℚ_[p])ˣ))⁻¹, (mem_integers_iff _).mpr u.property.2⟩
    val_inv := by ext; simp
    inv_val := by ext; simp }
  invFun u : evaluatedUnitSubgroup p := ⟨
    ⟨(u : (Integers (AlgebraicClosure ℚ_[p]))ˣ),
      (u : (Integers (AlgebraicClosure ℚ_[p]))ˣ).property⟩,
    (mem_integers_iff _).mp
      ((u : (Integers (AlgebraicClosure ℚ_[p]))ˣ).property),
    (mem_integers_iff _).mp
      ((u⁻¹ : (Integers (AlgebraicClosure ℚ_[p]))ˣ).property)⟩
  left_inv u := by ext; rfl
  right_inv u := by ext; rfl
  map_mul' u v := by ext; rfl

noncomputable def localUnitsEquivOtriUnits :
    (Otri p)ˣ ≃* (Integers (AlgebraicClosure ℚ_[p]))ˣ :=
  (unitEvaluationEquiv p).trans (evaluatedUnitsEquivIntegersUnits p)

noncomputable def S2046LocalUnitsEquivOtriUnits :
    (Otri p)ˣ ≃* LocalOFieldUnits p :=
  localUnitsEquivOtriUnits p

#check localUnitsEquivOtriUnits
#check S2046LocalUnitsEquivOtriUnits
#print axioms localUnitsEquivOtriUnits

end LeanFormal.IUT.XiFPaper.S2046M1LocalUnitsActual

end