import tmp.sheaf.xif.paper.S2596uHMTActual
import tmp.sheaf.xif.paper.S2596rLiftTLAuxActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596vTInstancesActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2596uHMTActual
open LeanFormal.IUT.XiFPaper.S2596rLiftTLAuxActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
noncomputable instance instIsLoc : IsLocalization
    (Algebra.algebraMapSubmonoid S2594LP0PActual.OL
      (Submonoid.powers (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C)))
    S2594LP0PActual.T := by
  rw [S2596uHMTActual.hMT']
  infer_instance
local instance instAlgCT : Algebra S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.T :=
  S2599TInstancesActual.gCT.toAlgebra
noncomputable instance instTowerC : IsScalarTower S2565ConcreteIntegralClosureCActual.C
    S2594LP0PActual.OL S2594LP0PActual.T :=
  IsScalarTower.of_algebraMap_eq' rfl
end LeanFormal.IUT.XiFPaper.S2596vTInstancesActual
end

