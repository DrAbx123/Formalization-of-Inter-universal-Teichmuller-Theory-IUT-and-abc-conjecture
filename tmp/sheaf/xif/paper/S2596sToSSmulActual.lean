import tmp.sheaf.xif.paper.S2596qNaturalActual
import tmp.sheaf.xif.paper.S2597RootSetEquivActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596sToSSmulActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual
open LeanFormal.IUT.XiFPaper.S2596qNaturalActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596rLiftTLAuxActual
open LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) S2594LP0PActual.OL :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field S2057FiveDivisionField
local instance : SMulCommClass Gal(S2057FiveDivisionField/S1720Field) (RingOfIntegers S1720Field) S2594LP0PActual.OL :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field S2057FiveDivisionField
variable (f : S2565ConcreteIntegralClosureCActual.S[X])
  (hmonic : f.Monic) (hdeg : f.natDegree ≠ 0)
  (hsplit : (f.map (algebraMap S2565ConcreteIntegralClosureCActual.S S2057FiveDivisionField)).Splits)
lemma toS_smul
    (sigma : Gal(S2057FiveDivisionField/S1720Field))
    (x : f.rootSet S2057FiveDivisionField) :
    S2597RootSetEquivActual.toS (R := S2565ConcreteIntegralClosureCActual.S)
        (S := S2594LP0PActual.T) (L := S2057FiveDivisionField)
        f hmonic hdeg (sigma • x) =
      sigma • (S2597RootSetEquivActual.toS (R := S2565ConcreteIntegralClosureCActual.S)
        (S := S2594LP0PActual.T) (L := S2057FiveDivisionField)
        f hmonic hdeg x) := by
  apply IsFractionRing.injective S2594LP0PActual.T S2057FiveDivisionField
  rw [S2597RootSetEquivActual.toS_val]
  rw [algebraMap_smul_T]
  rw [S2597RootSetEquivActual.toS_val]
#print axioms toS_smul
end LeanFormal.IUT.XiFPaper.S2596sToSSmulActual
end
