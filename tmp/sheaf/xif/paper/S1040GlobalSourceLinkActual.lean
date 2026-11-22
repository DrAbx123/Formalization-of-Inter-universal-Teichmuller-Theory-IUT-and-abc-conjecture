import tmp.sheaf.xif.paper.S1038GlobalSourceQFinalActual
import tmp.sheaf.xif.paper.S1039PaperQFieldAuditActual

/-! # S1040: global paper qPilot field and final Cor312

The paper qPilot object is global: the correct link field is
  O.qPilotLogVolume = globalQPilotLog T,
not the local paperQPilotLogVolume C3.

The existing S1024/S995 assembly consumes the original PaperXiFSourceLink whose
paper field is local.  It cannot be retyped here without a globalized assembly.
Therefore the final Cor312 keeps exactly one explicit local paper-field bridge
  S1040OriginalLinkBridgeRequired : O.qPilotLogVolume = paperQPilotLogVolume C3
while the link identification itself is the GLOBAL comparison (S1038), proved
from S1037.  No local=global fake is asserted; the bridge is an explicit exact
input, not a theorem. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1040GlobalSourceLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S1024FinalCor312Actual
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S1038GlobalSourceQFinalActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S1039PaperQFieldAuditActual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel u uC3 uD3 uM uP

variable {l : PrimeGeFive}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData (V := FinitePrimePlace 2 7) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Correct global paper qPilot field (replaces the local paperQPilotLogVolume). -/
def S1040GlobalPaperQField : Prop :=
  O.qPilotLogVolume = globalQPilotLog (l := l) T

/-- Exact bridge forced by the ORIGINAL link interface: its paper field is
local paperQPilotLogVolume C3. -/
def S1040OriginalLinkBridgeRequired : Prop :=
  O.qPilotLogVolume = paperQPilotLogVolume C3

/-- Global link identification: the paper comparison with the global qPilot. -/
def S1040GlobalLinkIdentification : Prop :=
  P.procession.average ≤ -O.qPilotLogVolume

/-- Actual global link identification from the S1037 corrected bridge and the
global q field. -/
theorem s1040GlobalLinkIdentification_of_bridge
    (In : S994FiniteInput T)
    (hb : S1037CorrectedBridge (l := l) P T In)
    (hglobal : S1040GlobalPaperQField (l := l) O T) :
    S1040GlobalLinkIdentification (l := l) P O := by
  unfold S1040GlobalLinkIdentification S1040GlobalPaperQField at *
  have h := s1037GlobalComparison_of_bridge (l := l) P T In hb
  linarith

/-- Final Cor312 with the global link identification.  The original assembly
still receives the exact local paper-field bridge; no fake local=global. -/
theorem s1040FinalCor312
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S1040OriginalLinkBridgeRequired (l := l) O C3)
    (In : S994FiniteInput T)
    (hb : S1037CorrectedBridge (l := l) P T In)
    (hglobal : S1038GlobalQIdentification (l := l) O
      (PaperLevelXiFTargetProofActual.globalQPilotLog (l := l) T))
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s968Inclusion
          P O C3
          (s1038Link (l := l) P O C3 T hident hqpaper In hb hglobal)
          (s1038Link_identification (l := l) P O C3 T
            hident hqpaper In hb hglobal)))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s968Inclusion
          P O C3
          (s1038Link (l := l) P O C3 T hident hqpaper In hb hglobal)
          (s1038Link_identification (l := l) P O C3 T
            hident hqpaper In hb hglobal)))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s968Inclusion
              P O C3
              (s1038Link (l := l) P O C3 T hident hqpaper In hb hglobal)
              (s1038Link_identification (l := l) P O C3 T
                hident hqpaper In hb hglobal))) links)) :=
  s1038FinalCor312 (l := l) P O C3 T hident hqpaper In hb hglobal links

end LeanFormal.IUT.XiFPaper.S1040GlobalSourceLinkActual

end
