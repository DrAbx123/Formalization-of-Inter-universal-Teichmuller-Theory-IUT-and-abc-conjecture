import tmp.sheaf.xif.paper.Mzk1P7MultiradialGeneralBridgeActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmReduction

/-!
# GAP-P7-MULTIRADIAL: finite witness for the general interface

GeneralMultiradialWitness is instantiated with the actual finite Q(i)-at-5
label/procession data: Label := SourceFiniteParameterized.Label l,
Choice := SourceFiniteParameterized.Choice l, carrier := carrier l, and
routeNormalForm := routeNormalForm_finite l.  This is a genuine witness for
the finite data in the general interface, not a general production.

FiniteIndeterminacyDischarge cannot be generalized as-is: it is defined with
the concrete ProcessionChoice and upperSemiLevel, not an arbitrary Carrier.
Core alone has no level-separation/injectivity axioms, so no general witness
is derivable from the frozen kernel interface.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.SourceFiniteParameterized

variable {l : PrimeGeFive}

/-- Finite Q(i)-at-5 data packaged as a GeneralMultiradialWitness. -/
noncomputable def finiteGeneralWitness (l : PrimeGeFive) :
    LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialGeneralBridgeActual.GeneralMultiradialWitness
      (Label := SourceFiniteParameterized.Label l)
      (Choice := SourceFiniteParameterized.Choice l) where
  carrier := SourceFiniteParameterized.carrier l
  routeNormalForm :=
    LeanFormal.IUT.MultiradialAlgorithmReduction.routeNormalForm_finite l

theorem finiteGeneralWitness_contract (l : PrimeGeFive) :
    LeanFormal.IUT.MultiradialAlgorithmReduction.CarrierAlgorithmContract
      (LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialGeneralBridgeActual.GeneralMultiradialWitness.carrier
        (finiteGeneralWitness l)) ∧
      LeanFormal.IUT.MultiradialAlgorithmReduction.RouteNormalForm
        (LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialGeneralBridgeActual.GeneralMultiradialWitness.carrier
          (finiteGeneralWitness l)) :=
  LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialGeneralBridgeActual.general_contract_and_routeNormalForm
    (W := finiteGeneralWitness l)

#print axioms finiteGeneralWitness_contract

end LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialWitnessActual
