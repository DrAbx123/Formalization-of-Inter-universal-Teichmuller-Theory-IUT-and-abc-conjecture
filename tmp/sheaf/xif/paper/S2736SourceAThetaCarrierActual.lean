import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaObjectActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2736SourceAThetaCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open LeanFormal.IUT.ThetaFieldTower
open ABCBridge.SourceQlThetaObjectActual

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

/-- Minimal source-side ATheta carrier: the actual curve, arithmetic divisor
type/degree/Galois predicate, source integral units and product-formula
normalization.  It deliberately has no geometric line-bundle or theta-structure
field; those are the exact missing objects. -/
structure SourceAThetaCarrier where
  baseField : Type u
  baseField_eq : baseField = S.arithmetic.F
  thetaField : Type u
  thetaField_eq : thetaField = S.arithmetic.K
  curve : PuncturedEllipticCurve S.arithmetic.F
  curve_eq : curve = S.arithmetic.curve
  divisorType : Type u
  divisorType_eq : divisorType = SourceThetaDivisor S
  degree : SourceThetaDivisor S -> Int
  degree_eq : degree = sourceThetaDegree S
  divisor : SourceThetaDivisor S
  divisor_eq : divisor = sourceThetaObjectZeroDivisor S
  divisor_degree_zero : degree divisor = 0
  galoisInvariant : SourceThetaDivisor S -> Prop
  galoisInvariant_eq : galoisInvariant = sourceGaloisInvariant S
  divisor_galois : galoisInvariant divisor
  integralUnits : Type u
  integralUnits_eq : integralUnits = SourceIntegralUnits S
  unitLog : NumberField.InfinitePlace S.arithmetic.F -> SourceIntegralUnits S -> Real
  unitLog_eq : unitLog = sourceIntegralUnitLog S
  globalNormalization : SourceIntegralUnits S -> Prop
  globalNormalization_eq : globalNormalization = sourceGlobalNormalization S

/-- The actual source-side minimal ATheta carrier. -/
noncomputable def sourceAThetaCarrier : SourceAThetaCarrier S where
  baseField := S.arithmetic.F
  baseField_eq := rfl
  thetaField := S.arithmetic.K
  thetaField_eq := rfl
  curve := S.arithmetic.curve
  curve_eq := rfl
  divisorType := SourceThetaDivisor S
  divisorType_eq := rfl
  degree := sourceThetaDegree S
  degree_eq := rfl
  divisor := sourceThetaObjectZeroDivisor S
  divisor_eq := rfl
  divisor_degree_zero := sourceThetaObjectZeroDivisor_degree S
  galoisInvariant := sourceGaloisInvariant S
  galoisInvariant_eq := rfl
  divisor_galois := sourceThetaObjectZeroDivisor_galois S
  integralUnits := SourceIntegralUnits S
  integralUnits_eq := rfl
  unitLog := sourceIntegralUnitLog S
  unitLog_eq := rfl
  globalNormalization := sourceGlobalNormalization S
  globalNormalization_eq := rfl

theorem sourceAThetaCarrier_divisorType :
    (sourceAThetaCarrier S).divisorType =
      (NumberField.InfinitePlace S.arithmetic.F -> Int) := rfl

theorem sourceAThetaCarrier_integralUnits :
    (sourceAThetaCarrier S).integralUnits =
      (NumberField.RingOfIntegers S.arithmetic.F)ˣ := rfl

theorem sourceAThetaCarrier_curve :
    (sourceAThetaCarrier S).curve = S.arithmetic.curve := rfl

/-- The minimal source ATheta carrier is actual and records the exact six
missing geometric/data items; no line-bundle carrier is asserted. -/
theorem sourceAThetaCarrier_missing_length :
    (sourceThetaObjectMissingData S).length = 6 :=
  sourceThetaObjectMissingData_length S

#check SourceAThetaCarrier
#check sourceAThetaCarrier
#check sourceAThetaCarrier_divisorType
#check sourceAThetaCarrier_integralUnits
#check sourceAThetaCarrier_curve
#check sourceAThetaCarrier_missing_length
#print axioms sourceAThetaCarrier_divisorType

end LeanFormal.IUT.XiFPaper.S2736SourceAThetaCarrierActual
end
