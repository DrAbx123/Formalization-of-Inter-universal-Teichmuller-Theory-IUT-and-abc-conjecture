import tmp.sheaf.xif.paper.S2657GeneralizedRootActual
import tmp.sheaf.xif.paper.S2574LocalizedP12Actual

noncomputable section
set_option maxHeartbeats 8000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace LeanFormal.IUT.XiFPaper.S2658LocalizedSplitsActual

theorem S2658_map_map_splits_iff
    {R : Type} [CommRing R] [Algebra R S1720Field]
    [Algebra R S2057FiveDivisionField]
    [IsScalarTower R S1720Field S2057FiveDivisionField]
    (f : R[X]) :
    (f.map (algebraMap R S2057FiveDivisionField)).Splits ↔
      ((f.map (algebraMap R S1720Field)).map
        (algebraMap S1720Field S2057FiveDivisionField)).Splits := by
  have hcomp : (algebraMap S1720Field S2057FiveDivisionField).comp
      (algebraMap R S1720Field) = algebraMap R S2057FiveDivisionField := by
    ext x
    exact (IsScalarTower.algebraMap_apply R S1720Field
      S2057FiveDivisionField x).symm
  rw [Polynomial.map_map, hcomp]

theorem S2658_S2574f_hsplit_iff :
    (S2574f.map (algebraMap S S2057FiveDivisionField)).Splits ↔
      ((S2574f.map (algebraMap S S1720Field)).map
        (algebraMap S1720Field S2057FiveDivisionField)).Splits :=
  S2658_map_map_splits_iff (R := S) S2574f

#check S2658_map_map_splits_iff
#check S2658_S2574f_hsplit_iff
#print axioms S2658_S2574f_hsplit_iff

end LeanFormal.IUT.XiFPaper.S2658LocalizedSplitsActual
end
