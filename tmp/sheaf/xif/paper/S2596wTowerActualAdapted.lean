import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2596rLiftTLAuxActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596wTowerActualAdapted
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2596rLiftTLAuxActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
noncomputable instance instAlgCT : Algebra S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.T :=
  S2599TInstancesActual.gCT.toAlgebra
noncomputable instance instTowerC : IsScalarTower S2565ConcreteIntegralClosureCActual.C
    S2594LP0PActual.OL S2594LP0PActual.T := by
  apply IsScalarTower.of_algebraMap_eq'
  intro x
  change S2599TInstancesActual.gCT x =
    (algebraMap S2594LP0PActual.OL S2594LP0PActual.T)
      (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL x)
  rfl
end LeanFormal.IUT.XiFPaper.S2596wTowerActualAdapted
end
