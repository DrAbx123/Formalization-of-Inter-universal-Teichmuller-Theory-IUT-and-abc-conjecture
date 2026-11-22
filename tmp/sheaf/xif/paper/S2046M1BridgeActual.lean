import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S2000CohomologicalPsiCnsActual
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitEvaluationImage

-- S2046 M1: exact bridge from LocalIntegralMonoid.evaluatedUnitSubgroup
-- to the actual algebraic-closure integral units.  The bridge is recorded
-- as the exact first missing; the conditional composition is actual.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046M1BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact M1 first missing: the evaluated integral-unit subgroup is the
    algebraic-closure integral-unit group.  The two definitions use
    IsIntegral over Z_p versus the norm≤1 model of Integers. -/
abbrev S2046EvaluatedUnitsToIntegersRequired : Type :=
  evaluatedUnitSubgroup p ≃* (Integers (AlgebraicClosure ℚ_[p]))ˣ

/-- Conditional actual composition: the exact bridge plus the library's
    unitEvaluationEquiv gives (Otri p)^x ≃* LocalOFieldUnits p. -/
noncomputable def S2046LocalUnitsEquivOtriUnitsOfBridge
    (e : S2046EvaluatedUnitsToIntegersRequired p) :
    (Otri p)ˣ ≃* LocalOFieldUnits p :=
  (unitEvaluationEquiv p).trans e

/-- The composite acts through the library unit evaluation. -/
theorem S2046LocalUnitsEquivOtriUnitsOfBridge_apply
    (e : S2046EvaluatedUnitsToIntegersRequired p) (u : (Otri p)ˣ) :
    (S2046LocalUnitsEquivOtriUnitsOfBridge p e u : LocalOFieldUnits p) =
      e (unitEvaluationEquiv p u) := rfl

/-- Actual library identification of Otri p units with the evaluated
    subgroup. -/
noncomputable abbrev S2046OtriUnitsEquivEvaluated :
    (Otri p)ˣ ≃* evaluatedUnitSubgroup p :=
  unitEvaluationEquiv p

#check S2046EvaluatedUnitsToIntegersRequired
#check S2046LocalUnitsEquivOtriUnitsOfBridge
#check S2046LocalUnitsEquivOtriUnitsOfBridge_apply
#check S2046OtriUnitsEquivEvaluated
#print axioms S2046LocalUnitsEquivOtriUnitsOfBridge

end LeanFormal.IUT.XiFPaper.S2046M1BridgeActual

end