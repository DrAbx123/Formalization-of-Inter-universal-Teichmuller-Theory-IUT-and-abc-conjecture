/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P7ContractLinkageWiringActual
import tmp.sheaf.xif.paper.Mzk1P7ContractB5EvidenceActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexConsumerActual
import Mathlib.Tactic

/-! # P7: Cor312 / 3.12 consumer chain over the completed B5Index + evidence layers -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312B5IndexChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312S3137AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractFieldsActualActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractLinkageWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractB5EvidenceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17BothResidueFieldInputsGapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

variable [Fintype (Bad (nativePlaceSelection T))]

/-- Cor 3.12 from the comparison, using the real-evidence StepXI contract. -/
theorem cor312_chain_contract (h : qThetaPilotLogVolumeComparison C3 P) :
    Cor312Conclusion (contractOfContractFieldsActual C3 P
      (contractFieldsActualOfComparison C3 P h)) :=
  cor312_of_contractFieldsActual C3 P (contractFieldsActualOfComparison C3 P h)

/-- The B5 residue-gap evidence from the comparison and residue-field inputs. -/
theorem cor312_chain_residue_gap
    (h : qThetaPilotLogVolumeComparison C3 P)
    (hbase : NativeBaseResidueFieldEquivInput T)
    (hF : QVFamResidueFieldEquivInput T) :
    ResNormDegreeGap T :=
  contractEvidenceWithB5_cor312_and_gap (h := h) (hbase := hbase) (hF := hF)

/-- The B5Index rank-one SNF datum and localized-count semantics for a nonzero
integral ideal of the arithmetic field. -/
theorem cor312_chain_b5Index
    (J : Ideal (NumberField.RingOfIntegers T.arithmetic.K)) (hJ : J ≠ 0)
    (v : NumberField.FinitePlace T.arithmetic.K) :
    Nonempty (Mzk1Ob33B5IndexActual.PlaceSNFData
        (J : LineBundle (k := T.arithmetic.K)) v) ∧
      exists (pi : LocalRing v) (e : Nat),
        e = (Associates.mk v.maximalIdeal.asIdeal).count (Associates.mk J).factors ∧
        localizedLine (k := T.arithmetic.K) (J : LineBundle (k := T.arithmetic.K)) v =
          Submodule.span (LocalRing v) {((pi : LocalField v) ^ e)} :=
  b5Index_placeSNFData_and_localizedCount J hJ v

def cor312ChainRows : List (String × String × String) :=
  [ ("cor312_chain_contract", "Cor312 from real-evidence contract", "PROVED (conditional on h)"),
    ("cor312_chain_residue_gap", "ResNormDegreeGap from B5 evidence", "PROVED (conditional on h, hbase, hF)"),
    ("cor312_chain_b5Index", "B5Index SNF + localized count (given hJ)", "PROVED") ]

theorem cor312ChainRows_length : cor312ChainRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312B5IndexChainActual

end