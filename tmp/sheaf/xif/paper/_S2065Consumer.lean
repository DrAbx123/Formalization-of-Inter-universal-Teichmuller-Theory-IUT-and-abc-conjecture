import tmp.sheaf.xif.paper.S2065IsometricClosureActual
import tmp.sheaf.xif.paper.S2040NormBridgeS2056Actual

noncomputable section
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2057NormBridgeFromIsometry
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2065IsometricClosureActual

namespace S2065Consumer

variable (place : NumberField.FinitePlace ℚ)
variable (v : FinitePrimePlace 2 7)

example : S2056ClosureIsometry place := S2065ClosureIsometry place
example : S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place :=
  S2065IntegralUnitsEquiv place
example : Nonempty (S2055IntegralUnitsIdentificationRequired place) :=
  S2065IntegralUnitsIdentification place
example : S2046NormBridge v := S2065NormBridgeOf v

-- the older S2040 consumer now accepts the isometry unconditionally
example : S2046NormBridge v :=
  LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual.s2040NormBridgeOfS2056Isometry
    v (S2065ClosureIsometry (QPlace v))

#print axioms LeanFormal.IUT.XiFPaper.S2065IsometricClosureActual.S2065ClosureIsometry

end S2065Consumer
end
