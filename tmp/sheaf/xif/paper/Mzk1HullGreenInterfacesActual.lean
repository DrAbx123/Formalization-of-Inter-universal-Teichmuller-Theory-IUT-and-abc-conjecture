/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: hull green interface list for #5/#6 (audit-only) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullGreenInterfacesActual

def hullGreenInterfaces : List String :=
  [ "Mzk1PaperVFactorActual (PaperVFactorData, inhabitant missing)" ,
    "Mzk1C3DIndexDataActual (C3DIndexData, inhabitant missing)" ,
    "Mzk1StepXIContractSchemaActual (ContractFieldSchema, evidence all none)" ,
    "Mzk1StepXIContractLinkageActual (ContractFieldsLinked false)" ,
    "Mzk1PaperIQCarrierInterfaceActual (PaperIQCarrierData, inhabitant missing)" ,
    "Mzk1PaperNormalizationDictionaryActual (PaperNormalizationData, inhabitant missing)" ]

theorem hullGreenInterfaces_length : hullGreenInterfaces.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HullGreenInterfacesActual