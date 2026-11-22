import tmp.sheaf.xif.paper.S2596cDenomClearActual
import tmp.sheaf.xif.paper.S2596bConcreteFixesCActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2596bConcreteFixesCActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
abbrev aOL : OL := algebraMap C OL Cden
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
lemma hfix (sigma : Gal(S2057FiveDivisionField/S1720Field)) :
    sigma • aOL = aOL := by
  simpa [aOL] using galois_fixes_algebraMap_C_Fp sigma (Cden : C)
lemma hfix' (sigma : Gal(S2057FiveDivisionField/S1720Field)) :
    (AlgEquiv.toRingEquiv sigma).toMonoidHom aOL = aOL := by
  simpa [AlgEquiv.toRingEquiv, MulSemiringAction.toRingEquiv] using hfix sigma
#print axioms hfix
#print axioms hfix'
end LeanFormal.IUT.XiFPaper.S2596dHfixActual
end
