import tmp.sheaf.xif.paper.S2596eSigmaEquivHomActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596fSmulUActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
lemma sigmaRingEquiv_u (sigma : Gal(S2057FiveDivisionField/S1720Field)) :
    sigmaRingEquiv sigma u = u := by
  have h1 : sigmaRingEquiv sigma (algebraMap OL T S2596cDenomClearActual.aOL) *
      sigmaRingEquiv sigma u = 1 := by
    rw [← map_mul, hu, map_one]
  rw [sigmaRingEquiv_apply_algebraMap, eSigma_aOL] at h1
  have hunit : IsUnit (algebraMap OL T S2596cDenomClearActual.aOL) :=
    IsUnit.of_mul_eq_one _ hu
  have h2 : algebraMap OL T S2596cDenomClearActual.aOL * sigmaRingEquiv sigma u =
      algebraMap OL T S2596cDenomClearActual.aOL * u := by
    rw [hu]; exact h1
  exact IsUnit.mul_left_cancel hunit h2
#print axioms sigmaRingEquiv_u
end LeanFormal.IUT.XiFPaper.S2596fSmulUActual
end
