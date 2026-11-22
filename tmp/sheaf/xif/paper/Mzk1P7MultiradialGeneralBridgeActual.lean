import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmReduction

/-!
# GAP-P7-MULTIRADIAL: general-vs-finite assumption bridge

The finite discharge `finiteMultiradialAlgorithmDischarge` has assumptions:
* `l : PrimeGeFive`;
* the concrete finite Q(i)-at-5 carrier `SourceFiniteParameterized.carrier l`;
* finite label group `Fl l = ZMod l` (commutative).

At the general `ParametricTheorem311.Carrier` level only the algorithm
contract is unconditional.  This file packages the explicit residual general
input `RouteNormalForm` as a named field; `FiniteIndeterminacyDischarge` has no
general-label analogue in the tree.  It is not an actual production theorem.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialGeneralBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.ParametricTheorem311

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- General carrier plus the one missing structural input: route normal form.
The Ind1/2/3 finite discharge still has no general-label analogue. -/
structure GeneralMultiradialWitness where
  carrier : ParametricTheorem311.Carrier Label Choice
  routeNormalForm :
    LeanFormal.IUT.MultiradialAlgorithmReduction.RouteNormalForm carrier

variable (W : GeneralMultiradialWitness (Label := Label) (Choice := Choice))

theorem general_algorithmContract :
    LeanFormal.IUT.MultiradialAlgorithmReduction.CarrierAlgorithmContract W.carrier :=
  LeanFormal.IUT.MultiradialAlgorithmReduction.carrierAlgorithmContract W.carrier

theorem general_contract_and_routeNormalForm :
    LeanFormal.IUT.MultiradialAlgorithmReduction.CarrierAlgorithmContract W.carrier ∧
      LeanFormal.IUT.MultiradialAlgorithmReduction.RouteNormalForm W.carrier :=
  ⟨general_algorithmContract (W := W), W.routeNormalForm⟩

#print axioms general_algorithmContract
#print axioms general_contract_and_routeNormalForm

end LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialGeneralBridgeActual
