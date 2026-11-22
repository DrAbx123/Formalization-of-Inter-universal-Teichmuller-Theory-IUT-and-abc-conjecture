import tmp.sheaf.xif.paper.S2536LocalizedPowersActual
import tmp.sheaf.xif.paper.S2610TTPrimeActual
import tmp.sheaf.xif.paper.S2594LP0PActual
import tmp.sheaf.xif.paper.S2562HZcMonicCActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596yTPrimeIntegralActualAdapted
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2610TTPrimeActual
open LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
noncomputable instance : IsIntegralClosure S2610TTPrimeActual.T'
    S2565ConcreteIntegralClosureCActual.S S2057FiveDivisionField :=
  S2536LocalizedPowersActual.isIntegralClosure_localization_powers
    (A := S2565ConcreteIntegralClosureCActual.C)
    (C := S2594LP0PActual.OL)
    (K := S1720Field)
    (L := S2057FiveDivisionField)
    (R := S2565ConcreteIntegralClosureCActual.S)
    (S := S2610TTPrimeActual.T')
    (a := (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C))
    (by exact mem_nonZeroDivisors_of_ne_zero (Int.cast_ne_zero.mpr S2562HZcMonicCActual.Cden_ne_zero))
    (hACL := by infer_instance)
    (hARS := by infer_instance)
    (hACS := by infer_instance)
    (hARL := by infer_instance)
    (hCSL := by infer_instance)
    (hRSL := by infer_instance)
end LeanFormal.IUT.XiFPaper.S2596yTPrimeIntegralActualAdapted
end
