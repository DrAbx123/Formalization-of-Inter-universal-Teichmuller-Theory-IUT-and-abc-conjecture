import tmp.sheaf.xif.paper.S2599TInstancesActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2597aSLTowerActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
lemma liftST_comp :
    S2599TInstancesActual.liftST.comp
      (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S) =
    S2599TInstancesActual.gCT :=
  IsLocalization.lift_comp (fun y => S2599TInstancesActual.gCT_unit y.1 y.2)
noncomputable instance instAlgSL : Algebra S2565ConcreteIntegralClosureCActual.S
    S2057FiveDivisionField :=
  ((algebraMap S2599TInstancesActual.OL S2057FiveDivisionField).comp
    S2599TInstancesActual.liftST).toAlgebra
noncomputable instance towerCSL : IsScalarTower S2565ConcreteIntegralClosureCActual.C
    S2565ConcreteIntegralClosureCActual.S S2057FiveDivisionField := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change algebraMap S2565ConcreteIntegralClosureCActual.C S2057FiveDivisionField x =
    (algebraMap S2565ConcreteIntegralClosureCActual.S S2057FiveDivisionField)
      (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S x)
  rw [show algebraMap S2565ConcreteIntegralClosureCActual.S S2057FiveDivisionField =
    (algebraMap S2599TInstancesActual.OL S2057FiveDivisionField).comp
      S2599TInstancesActual.liftST from rfl]
  rw [RingHom.comp_apply, RingHom.comp_apply, liftST_comp]
  change algebraMap S2565ConcreteIntegralClosureCActual.C S2057FiveDivisionField x =
    (algebraMap S2599TInstancesActual.OL S2057FiveDivisionField)
      (S2599TInstancesActual.gCT x)
  rw [show S2599TInstancesActual.gCT x =
    algebraMap S2599TInstancesActual.OL S2594LP0PActual.T
      (algebraMap S2565ConcreteIntegralClosureCActual.C S2599TInstancesActual.OL x) from rfl]
  rw [IsScalarTower.algebraMap_apply S2565ConcreteIntegralClosureCActual.C
    S2599TInstancesActual.OL S2057FiveDivisionField]
#print axioms liftST_comp
end LeanFormal.IUT.XiFPaper.S2597aSLTowerActual
end
