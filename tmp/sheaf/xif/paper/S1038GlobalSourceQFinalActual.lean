import tmp.sheaf.xif.paper.S1024FinalCor312Actual
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.paper.S1037GlobalQPilotAuditActual
import tmp.sheaf.xif.paper.ThetaLinkFromSource

/-! # S1038: final Cor312 with GLOBAL sourceQ/hQ

The paper qPilot object is global: S706 globalQPilotLog T = weighted sum of
perBQPilotLog, while C3.q is a single local q.  We replace the local
thetaSourceComparison link by the global comparison
  P.procession.average ≤ -globalQPilotLog T
proved from S1037CorrectedBridge, and identify the legacy global qPilot scalar
O.qPilotLogVolume with globalQPilotLog T.

The resulting link's identification is the global comparison; S1024 then gives
the final Cor312.  The link's paper-q field O.q = paperQPilotLogVolume C3 remains
an exact input (it is the local paper normalization field of the link
structure); no local=global Oa fake is used. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1038GlobalSourceQFinalActual

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
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S1024FinalCor312Actual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
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

/-- Exact global qPilot identification: the legacy global scalar is S706's
global qPilot log. -/
def S1038GlobalQIdentification (Qglobal : Real) : Prop :=
  O.qPilotLogVolume = Qglobal

/-- Corrected link with global comparison as link identification. -/
noncomputable def s1038Link
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (In : S994FiniteInput T)
    (hb : S1037CorrectedBridge (l := l) P T In)
    (hglobal : S1038GlobalQIdentification (l := l) O (PaperLevelXiFTargetProofActual.globalQPilotLog (l := l) T)) :
    PaperXiFSourceLink O P C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper := hqpaper
  link_identification := P.procession.average ≤ -O.qPilotLogVolume
  link_implies_inclusion := by
    intro hcomp
    rw [mem_hullLogVolumeRay_iff, P.signedHullLogVolume_eq_neg_average]
    linarith

/-- The global comparison holds from the corrected S1037 bridge and the global
identification. -/
theorem s1038Link_identification
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (In : S994FiniteInput T)
    (hb : S1037CorrectedBridge (l := l) P T In)
    (hglobal : S1038GlobalQIdentification (l := l) O (PaperLevelXiFTargetProofActual.globalQPilotLog (l := l) T)) :
    (s1038Link (l := l) P O C3 T hident hqpaper In hb hglobal).link_identification := by
  show P.procession.average ≤ -O.qPilotLogVolume
  have h := s1037GlobalComparison_of_bridge (l := l) P T In hb
  change O.qPilotLogVolume =
    PaperLevelXiFTargetProofActual.globalQPilotLog (l := l) T at hglobal
  linarith [h, hglobal]

/-- Final Cor312 with the global sourceQ/hQ. -/
theorem s1038FinalCor312
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (In : S994FiniteInput T)
    (hb : S1037CorrectedBridge (l := l) P T In)
    (hglobal : S1038GlobalQIdentification (l := l) O (PaperLevelXiFTargetProofActual.globalQPilotLog (l := l) T))
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
  s1024FinalCor312 (l := l) (T := T) (P := P) (O := O) (C3 := C3)
    (s1038Link (l := l) P O C3 T hident hqpaper In hb hglobal)
    (s1038Link_identification (l := l) P O C3 T
      hident hqpaper In hb hglobal)
    links

end LeanFormal.IUT.XiFPaper.S1038GlobalSourceQFinalActual

end
