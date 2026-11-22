import tmp.sheaf.xif.paper.S2035ActualOUnitsMuActual
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual

#check GvEquiv
#check unitsEquiv_action
#print axioms GvEquiv
#print axioms unitsEquiv_action

-- The exact completion-side integral carrier that S2035 does not construct.
#check fun (v : FinitePrimePlace 2 7) => (Integers (Lv v))ˣ

-- The existing API already supplies the restricted Galois action on it.
#check fun (v : FinitePrimePlace 2 7) (sigma : Gv v) =>
  localGaloisUnitMap (K := Lv v) (p := (completionRationalPrime (QPlace v)).val)
    (sigma.restrictScalars (PadicScalarField (QPlace v)))

-- The Q_p model integral carrier of S1978 exists and is axiom-clean.
#check LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual.LocalOFieldUnits
#print axioms LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual.LocalOFieldUnitsAction
