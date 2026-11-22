import tmp.sheaf.xif.paper.S2056IsometricClosureActual
import tmp.sheaf.xif.paper.S2046CompletionOUnitsActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
namespace LeanFormal.IUT.XiFPaper.S2057NormBridgeFromIsometry
variable (v : FinitePrimePlace 2 7)
/-- A closure isometry gives the S2046 canonical norm/mu bridge. -/
noncomputable def S2057NormBridgeOfIsometry
    (I : S2056ClosureIsometry (QPlace v)) :
    S2046NormBridge v where
  identification := S2056IntegralUnitsEquiv (QPlace v) I
  muCompatible :=
    QuotientGroup.congr
      (CommGroup.torsion (S2055CompletionIntegralUnits (QPlace v)))
      (CommGroup.torsion (S2055QpIntegralUnits (QPlace v)))
      (S2056IntegralUnitsEquiv (QPlace v) I)
      (S2056IntegralUnitsEquiv (QPlace v) I).map_torsion
theorem S2057NormBridgeOfIsometry_available
    (h : Nonempty (S2056ClosureIsometry (QPlace v))) :
    Nonempty (S2046NormBridge v) :=
  h.elim fun I => ⟨S2057NormBridgeOfIsometry v I⟩
#check S2057NormBridgeOfIsometry
#check S2057NormBridgeOfIsometry_available
end LeanFormal.IUT.XiFPaper.S2057NormBridgeFromIsometry
end
