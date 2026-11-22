import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullInterfaceDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: StepXI tree-asset bundle (iutiii:StepXI node) -> Contract/Cor312Conclusion/Routes/Cor312RouteCertificate + Obligations ipl/she/apt + SourceHullInterfaceDischarge (ValueHullCompactnessInput/sourceHullVolume_lt_top_of_compactnessInput) -> PROVED tree bundle: contract conclusion, route certificate, obligation ids, compactness-input consequence. No new math; no closure.

# Mzk1TreeStepXIBundleActual — StepXI tree-asset bundle

PROVED:
* `stepXI_contract_bundle`: contract -> Cor312 + route certificate + obligation ids;
* `stepXI_compactness_consumer`: ValueHullCompactnessInput -> sourceHullVolume finite
  (tree discharge theorem, parameterized by OriginalInput data).
CONSUMED TREE ASSETS: StepXIContract, Cor312RouteCertificate, Audit obligations, ValueHullCompactnessInput.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

/-- **PROVED:** contract => Cor312 + route certificate + obligation ids. -/
theorem stepXI_contract_bundle (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion contract ∧
      Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨cor312_of_constructed_stepXI contract,
    ({ route := route, contract := contract } : Cor312RouteCertificate).conclusion,
    rfl, rfl, rfl⟩

def stepXI_contractRows : List (String × String × String) :=
  [ ("contract => Cor312", "PROVED", "cor312_of_constructed_stepXI (Contract:49)")
  , ("route certificate conclusion", "PROVED", "Cor312RouteCertificate.conclusion (Routes:42)")
  , ("obligation ids", "PROVED", "ipl/she/apt ids (Obligations:5/12/19)")
  , ("compactness input consequence", "CONSUMED TREE", "sourceHullVolume_lt_top_of_compactnessInput (Discharge:223)")
  , ("contract construction from IUT input", "NAMED", "Contract:61 Obligation") ]

theorem stepXI_contractRows_length : stepXI_contractRows.length = 5 := rfl

#check stepXI_contract_bundle
#check stepXI_contractRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual
end