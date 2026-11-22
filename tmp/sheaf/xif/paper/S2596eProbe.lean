import tmp.sheaf.xif.paper.S2596dHfixActual
noncomputable section
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596eProbe
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
#check hfix'
#check MulSemiringAction.toRingEquiv (G := Gal(S2057FiveDivisionField/S1720Field)) (R := OL)
#check RingEquiv.toMonoidHom
end LeanFormal.IUT.XiFPaper.S2596eProbe
end
