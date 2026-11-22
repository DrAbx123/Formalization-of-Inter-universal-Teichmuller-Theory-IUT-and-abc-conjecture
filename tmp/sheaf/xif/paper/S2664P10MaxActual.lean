import tmp.sheaf.xif.paper.S2663P10PrimeActual
import tmp.sheaf.xif.paper.S2537ConcreteLocalizationActual
import Mathlib.RingTheory.Ideal.GoingUp
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2664P10MaxActual
open LeanFormal.IUT.XiFPaper.S2663P10PrimeActual
open LeanFormal.IUT.XiFPaper.S2661P10Actual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
local instance : IsIntegralClosure LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S
    LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R S2057FiveDivisionField :=
  LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S2537_isIntegralClosure
local instance : Algebra.IsIntegral LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
    LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S :=
  IsIntegralClosure.isIntegral_algebra
    LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R S2057FiveDivisionField
theorem P10_isMaximal (W : S2584PrimeDegreeOneWitness) : (P10 W).IsMaximal :=
  haveI : (p10 W).IsMaximal := p10_isMaximal W
  haveI : (P10 W).IsPrime := P10_prime W
  haveI : (P10 W).LiesOver (p10 W) := P10_lies_p10 W
  Ideal.IsMaximal.of_liesOver_isMaximal (p := p10 W) (P := P10 W)
#print axioms P10_isMaximal
end LeanFormal.IUT.XiFPaper.S2664P10MaxActual
end
