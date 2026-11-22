import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlCarrierMap
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLinkBridge
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaObjectActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open ABCBridge.SourceQlCarrierMap
open ABCBridge.SourceQlThetaObjectActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2733MqMThetaActual

variable {F : Type} [Field F] [NumberField F]
variable (l : PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance s2733PrimeFact : Fact (Nat.Prime l.value) := l.factPrime

/-- The actual source q-side unit carrier: integral units of the actual source
local field Q_l. -/
abbrev Mq : Type := (Integers (sourceLocalField l))ˣ

/-- The actual theta-side comparison carrier: integral units of the actual
normalized completion at the chosen place. -/
abbrev MTheta : Type := (Integers (CommonPrimeCompletion place))ˣ

/-- The actual unit comparison Mq -> MTheta supplied by the source embedding. -/
noncomputable def unitComparisonMqMTheta : Mq l →* MTheta place :=
  sourceQlUnitMap l place

theorem unitComparisonMqMTheta_apply (u : Mq l) :
    ((unitComparisonMqMTheta l place u).val : CommonPrimeCompletion place) =
      sourceQlToTargetRingHom l place (u.val : sourceLocalField l) :=
  sourceQlUnitMap_val l place u

theorem unitComparisonMqMTheta_map_one :
    unitComparisonMqMTheta l place 1 = 1 :=
  map_one (unitComparisonMqMTheta l place)

theorem unitComparisonMqMTheta_map_mul (u v : Mq l) :
    unitComparisonMqMTheta l place (u * v) =
      unitComparisonMqMTheta l place u * unitComparisonMqMTheta l place v :=
  map_mul (unitComparisonMqMTheta l place) u v

/-- Actual source integral units of F: the carrier intended for the theta side
in the paper.  It is recorded, not mapped to Mq by an actual hom in this file. -/
abbrev SourceThetaUnits (S : SourceDefinition31Data l) : Type :=
  sourceThetaObjectIntegralUnits S

#check Mq
#check MTheta
#check unitComparisonMqMTheta
#check SourceThetaUnits
#print axioms unitComparisonMqMTheta_apply

end LeanFormal.IUT.XiFPaper.S2733MqMThetaActual
end
