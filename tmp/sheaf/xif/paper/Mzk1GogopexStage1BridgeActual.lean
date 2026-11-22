import tmp.sheaf.gogopex.Iut.Stage1.SourceObligations
import tmp.sheaf.gogopex.Iut.Stage1.IUTStage1Data
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gogopex Stage1 source obligations ↔ our StepXIContract

Real reference bridge: a completed `SourceObligationLedger` (IPL/SHE/APT and
charted pilot data) yields our StepXI contract, and its conclusion is the
Gogopex signed Cor 3.12 inequality.  Separately, `IUTStage1PreLedgerData`
exposes the structured IPL/SHE/APT fields as a real object. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GogopexStage1BridgeActual

open LeanFormal.IUT
open Iut
open Iut.Stage1

universe u

section SourceLedger

variable {source target : Copy} {index : Type u}
variable {output : AlgorithmicOutput source target index}
variable {measure : RegionMeasure target}
variable {thetaSigned qSigned : Real} {normalization : Prop}

/-- Build our StepXI contract from a completed source-obligation ledger. -/
def contractOfLedger
    (ledger : SourceObligationLedger output measure thetaSigned qSigned normalization) :
    StepXIContract where
  qSigned := qSigned
  thetaSigned := thetaSigned
  targetSigned := ledger.targetVolume.targetSigned
  q_negative := neg_pos.mp ledger.q_positive
  ipl := QualitativeData.HasStructuredIPL output.family
  she := QualitativeData.HasStructuredSHE output.family
  apt := QualitativeData.HasStructuredAPT output.family
  ipl_evidence := ledger.certificate.hasStructuredIPL
  she_evidence := ledger.certificate.hasStructuredSHE
  apt_evidence := ledger.certificate.hasStructuredAPT
  q_le_target := ledger.threeTermComparison.q_le_target
  target_le_theta := ledger.threeTermComparison.target_le_theta

theorem contractOfLedger_conclusion
    (ledger : SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Cor312Conclusion (contractOfLedger ledger) :=
  cor312_of_constructed_stepXI (contractOfLedger ledger)

theorem gogopexCorollary312_of_ledger
    (ledger : SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) :=
  corollary312_of_signed_le (contractOfLedger_conclusion ledger)

end SourceLedger

section PreLedger

variable {source target : Copy} {index : Type u}

/-- The structured IPL/SHE/APT data of a Stage1 pre-ledger, as an object. -/
structure StructuredStage1Obligations
    (data : IUTStage1PreLedgerData source target index) where
  ipl : QualitativeData.HasStructuredIPL data.output.family
  she : QualitativeData.HasStructuredSHE data.output.family
  apt : QualitativeData.HasStructuredAPT data.output.family

def structuredObligationsOfPreLedger
    (data : IUTStage1PreLedgerData source target index) :
    StructuredStage1Obligations data where
  ipl := data.hasStructuredIPL
  she := data.hasStructuredSHE
  apt := data.hasStructuredAPT

theorem structuredObligationsOfPreLedger_ipl
    (data : IUTStage1PreLedgerData source target index) :
    (structuredObligationsOfPreLedger data).ipl = data.hasStructuredIPL := rfl

end PreLedger

end LeanFormal.IUT.XiFPaper.Mzk1GogopexStage1BridgeActual

end
