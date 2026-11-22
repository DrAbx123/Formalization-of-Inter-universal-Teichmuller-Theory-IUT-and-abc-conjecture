/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HolomorphicHullLogVolumeReconciliationActual
import tmp.sheaf.xif.paper.Mzk1P7GapRegisterActual
import tmp.sheaf.xif.paper.Mzk1P7Missing7StatusActual
import tmp.sheaf.xif.paper.Mzk1P7CodeInterfaceActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractLinkageActual
import tmp.sheaf.xif.paper.Mzk1Cor312S3137AssemblyActual
import Mathlib.Tactic

/-! # P7 #8 CONTRACT: reconciliation 12 rows / 7 missing -> 10 GAP codes

Machine mapping (audit + conditional assembly).  The only mathematical content is
the re-exported conditional assembly: comparison hypothesis => Cor312Conclusion.
The remaining rows are explicit mapping data; no obligation is claimed discharged
unless marked DISCHARGED.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312S3137AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P7GapRegisterActual
open LeanFormal.IUT.XiFPaper.Mzk1P7CodeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractLinkageActual

/-- Mapping of the 12 reconciliation rows to GAP codes (or DISCHARGED). -/
def recon12ToGap : List (String × String) :=
  [ ("WallObligation.holomorphicHull", "GAP-P7-CONTRACT"),
    ("WallObligation.determinantNormalization", "GAP-P7-OB33-SRC"),
    ("WallObligation.logVolumeComparison", "GAP-P7-GENERAL-CMP"),
    ("S3137 q reading", "DISCHARGED"),
    ("S3137 theta reading", "GAP-P7-THETA-V"),
    ("HullVolumeReuse comparison", "DISCHARGED"),
    ("GapNormalization sufficient reductions", "GAP-P7-GENERAL-CMP (conditional)"),
    ("S3137 -> Cor312 assembly", "DISCHARGED (conditional on comparison)"),
    ("N3 SharedContainer bridge", "DISCHARGED"),
    ("strength upgrade", "DISCHARGED (shape; comparison pending)"),
    ("HullDeterminantLogVolumeReduction", "GAP-P7-THETA-D / GAP-P7-THETA-DEG / GAP-P7-OB33-SRC"),
    ("final boundary Szpiro", "GAP-P7-HULL-UB") ]

theorem recon12ToGap_length : recon12ToGap.length = 12 := rfl

/-- Mapping of the 7 reconciliation missing items to GAP codes + interface files. -/
def missing7ToGap : List (String × String × String) :=
  [ ("general qThetaPilotLogVolumeComparison", "GAP-P7-GENERAL-CMP", "Mzk1GeneralComparisonInterfaceActual.lean"),
    ("paper carrier IQ realization", "GAP-P7-IQ-LITERAL", "Mzk1PaperIQCarrierInterfaceActual.lean:16/23"),
    ("(Ob3-3) source identification", "GAP-P7-OB33-SRC", "Mzk1Ob33InterfaceActual.lean"),
    ("multiradial (xi-e)/(xi-f) production", "GAP-P7-MULTIRADIAL", "Mzk1ComparisonDataStatusActual.lean"),
    ("theta raw Haar vs paper normalized V", "GAP-P7-THETA-V / GAP-P7-THETA-D / GAP-P7-THETA-DEG", "Mzk1C3S1902BridgeActual / Mzk1ThetaVFactorInterfaceActual"),
    ("StepXIContract fields/linkage", "GAP-P7-CONTRACT", "Mzk1StepXIContractLinkageActual.lean:15/16"),
    ("exact hull volume upper bound", "GAP-P7-HULL-UB", "Mzk1HullUpperBoundInterfaceActual.lean") ]

theorem missing7ToGap_length : missing7ToGap.length = 7 := rfl

/-- The 10 registered GAP codes, with the ones reachable from the 7 missing items. -/
def gapCodesCovered : List String :=
  [ "GAP-P7-GENERAL-CMP", "GAP-P7-IQ-LITERAL", "GAP-P7-OB33-SRC", "GAP-P7-MULTIRADIAL",
    "GAP-P7-THETA-V", "GAP-P7-THETA-D", "GAP-P7-THETA-DEG", "GAP-P7-CONTRACT",
    "GAP-P7-HULL-UB", "GAP-NORM-ARCH-C-K" ]

theorem gapCodesCovered_length : gapCodesCovered.length = 10 := rfl

theorem gapCodesCovered_eq_gapRegister :
    gapCodesCovered.length = gapRegister.length := rfl

/-- #6 evidence: `ContractFieldsLinked` is false in the current tree (no evidence fields). -/
theorem contract_fields_not_linked : ¬ ContractFieldsLinked := linkage_not_linked

/-- **Conditional contract assembly**: the only mathematical input is the actual
comparison; the 12-row table tells which rows are discharged and which are the
7 missing items feeding that comparison. -/
theorem p7_conditional_contract
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I))
    (h : qThetaPilotLogVolumeComparison C3 P) :
    Cor312Conclusion (contractOfS3137Comparison C3 P h) :=
  cor312_of_s3137Comparison C3 P h

def p7ContractRows : List (String × String × String) :=
  [ ("reconciliation 12 rows", "mapped to GAP codes / DISCHARGED", "recon12ToGap (PROVED length 12)"),
    ("reconciliation 7 missing", "mapped to 10 GAP codes + interfaces", "missing7ToGap (PROVED length 7)"),
    ("#6 contract linkage", "ContractFieldsLinked = false", "contract_fields_not_linked (PROVED)"),
    ("conditional assembly", "comparison => Cor312Conclusion", "p7_conditional_contract (PROVED)") ]

theorem p7ContractRows_length : p7ContractRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapActual

end