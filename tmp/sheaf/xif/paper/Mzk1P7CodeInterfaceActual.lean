/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: GAP-code → addressable interface mapping (audit-only) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P7CodeInterfaceActual

def codeInterfaces : List (String × String × String) :=
  [ ("GAP-P7-GENERAL-CMP", "Mzk1GeneralComparisonInterfaceActual.lean", "GeneralQThetaComparison") ,
    ("GAP-P7-IQ-LITERAL", "Mzk1PaperIQCarrierInterfaceActual.lean:16/23", "PaperIQCarrierData (inhabitant missing)") ,
    ("GAP-P7-OB33-SRC", "Mzk1Ob33InterfaceActual.lean", "Ob33SourceIdentification") ,
    ("GAP-P7-MULTIRADIAL", "Mzk1ComparisonDataStatusActual.lean", "comparisonDataStatus") ,
    ("GAP-P7-THETA-V", "Mzk1ThetaVFactorInterfaceActual.lean", "ThetaVFactorIdentification") ,
    ("GAP-P7-THETA-D", "Mzk1C3DIndexDataActual.lean:15/21", "C3DIndexData (inhabitant missing)") ,
    ("GAP-P7-THETA-DEG", "Mzk1ThetaRawPacketFactorActual.lean", "rawThetaLogVolume_eq_dim_mul_candidateNormalized") ,
    ("GAP-P7-CONTRACT", "Mzk1StepXIContractLinkageActual.lean:7/15/16", "ContractFieldsLinked (false)") ,
    ("GAP-P7-HULL-UB", "Mzk1HullUpperBoundInterfaceActual.lean", "HullUpperBound") ,
    ("GAP-NORM-ARCH-C-K", "Mzk1NormArchCAbcActual.lean", "heightWeight_rat") ]

theorem codeInterfaces_length : codeInterfaces.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7CodeInterfaceActual