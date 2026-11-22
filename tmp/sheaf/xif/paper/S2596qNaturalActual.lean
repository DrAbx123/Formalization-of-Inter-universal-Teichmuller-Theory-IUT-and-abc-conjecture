import tmp.sheaf.xif.paper.S2596pReductionActual
import tmp.sheaf.xif.paper.S2361SmulActual
import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2596rLiftTLAuxActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596qNaturalActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596fSmulUActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S2361SmulActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
local instance : IsScalarTower S2594LP0PActual.OL S2594LP0PActual.T S2057FiveDivisionField := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change algebraMap S2594LP0PActual.OL S2057FiveDivisionField x =
    S2599TInstancesActual.liftTL (algebraMap S2594LP0PActual.OL S2594LP0PActual.T x)
  rw [← S2596rLiftTLAuxActual.liftTL'_eq]
  exact (RingHom.congr_fun S2596rLiftTLAuxActual.liftTL'_comp x).symm
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) S2594LP0PActual.OL :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field S2057FiveDivisionField
local instance : SMulCommClass Gal(S2057FiveDivisionField/S1720Field) (RingOfIntegers S1720Field) S2594LP0PActual.OL :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field S2057FiveDivisionField
lemma algebraMap_smul_T
    (sigma : Gal(S2057FiveDivisionField/S1720Field)) (a : S2594LP0PActual.T) :
    algebraMap S2594LP0PActual.T S2057FiveDivisionField (sigmaRingEquiv sigma a) =
      sigma (algebraMap S2594LP0PActual.T S2057FiveDivisionField a) := by
  let j : S2594LP0PActual.T →+* S2057FiveDivisionField :=
    (algebraMap S2594LP0PActual.T S2057FiveDivisionField).comp (sigmaRingEquiv sigma).toRingHom
  let k : S2594LP0PActual.T →+* S2057FiveDivisionField :=
    sigma.toRingHom.comp (algebraMap S2594LP0PActual.T S2057FiveDivisionField)
  have h : j = k := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers S2596cDenomClearActual.aOL)
    ext x
    change algebraMap S2594LP0PActual.T S2057FiveDivisionField
        (sigmaRingEquiv sigma (algebraMap S2594LP0PActual.OL S2594LP0PActual.T x)) =
      sigma (algebraMap S2594LP0PActual.T S2057FiveDivisionField
        (algebraMap S2594LP0PActual.OL S2594LP0PActual.T x))
    rw [sigmaRingEquiv_apply_algebraMap]
    rw [← IsScalarTower.algebraMap_apply S2594LP0PActual.OL
      S2594LP0PActual.T S2057FiveDivisionField]
    rw [← IsScalarTower.algebraMap_apply S2594LP0PActual.OL
      S2594LP0PActual.T S2057FiveDivisionField]
    simpa [eSigma, MulSemiringAction.toRingEquiv] using
      S2361_algebraMap_smul (K := S1720Field) (L := S2057FiveDivisionField) sigma x
  exact RingHom.congr_fun h a
#print axioms algebraMap_smul_T
end LeanFormal.IUT.XiFPaper.S2596qNaturalActual
end
