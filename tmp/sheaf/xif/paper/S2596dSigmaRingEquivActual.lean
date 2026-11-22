import tmp.sheaf.xif.paper.S2596dHfixActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596dSigmaRingEquivActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
noncomputable def eSigma (sigma : Gal(S2057FiveDivisionField/S1720Field)) : OL ≃+* OL :=
  MulSemiringAction.toRingEquiv (G := Gal(S2057FiveDivisionField/S1720Field)) (R := OL) sigma
lemma eSigma_aOL (sigma : Gal(S2057FiveDivisionField/S1720Field)) :
    eSigma sigma aOL = aOL := by
  change sigma • aOL = aOL
  exact hfix sigma
noncomputable def sigmaRingEquiv (sigma : Gal(S2057FiveDivisionField/S1720Field)) : T ≃+* T :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers aOL) (S := T) (T := Submonoid.powers aOL) T
    (eSigma sigma)
    (by
      rw [Submonoid.map_powers (eSigma sigma).toMonoidHom aOL]
      change Submonoid.powers ((eSigma sigma) aOL) = Submonoid.powers aOL
      rw [eSigma_aOL sigma])
#print axioms eSigma_aOL
#print axioms sigmaRingEquiv
end LeanFormal.IUT.XiFPaper.S2596dSigmaRingEquivActual
end
