import tmp.sheaf.xif.paper.S1038GlobalSourceQFinalActual
import tmp.sheaf.xif.PaperQPilotLogVolume

/-! # S1039: paperQPilotLogVolume is LOCAL, so hqpaper is an object mismatch

paperQPilotLogVolume C3 = localSignedLog C3.q (single finite-place scalar).
globalQPilotLog T is the global Bad-place weighted per-b qPilot log.
Therefore S1038's hqpaper
  O.qPilotLogVolume = paperQPilotLogVolume C3
identifies a global O scalar with a local paper scalar; together with the
global identification O.qPilotLogVolume = globalQPilotLog T it forces
paperQPilotLogVolume C3 = globalQPilotLog T, a local=global identification.

The S1024 link structure requires exactly this local field.  The corrected
global link structure, with the paper qPilot field replaced by
globalQPilotLog T, is recorded; S1024 cannot consume it without a globalized
assembly.  No fake equality. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1039PaperQFieldAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1038GlobalSourceQFinalActual
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

/-- paperQPilotLogVolume is defined as the single local q scalar. -/
theorem s1039PaperQPilotLogVolume_eq_local :
    paperQPilotLogVolume C3 = localSignedLog C3.q := rfl

/-- The paper qPilot scalar is local: it depends only on C3.q, not on Bad. -/
theorem s1039PaperQPilotLogVolume_local :
    paperQPilotLogVolume C3 = localSignedLog (C3.q) := rfl

/-- hqpaper plus the global identification forces the exact local=global
identification paperQPilotLogVolume = globalQPilotLog. -/
theorem s1039Hqpaper_forces_local_global
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hglobal : O.qPilotLogVolume = globalQPilotLog (l := l) T) :
    paperQPilotLogVolume C3 = globalQPilotLog (l := l) T := by
  rw [← hqpaper, hglobal]

/-- Exact local/global identification forced by the current link field. -/
def S1039LocalGlobalPaperQIdentification : Prop :=
  paperQPilotLogVolume C3 = globalQPilotLog (l := l) T

/-- Corrected global paper-q field: the link's paper scalar should be the
global qPilot log, not the local paperQPilotLogVolume C3. -/
def S1039GlobalPaperQIdentification : Prop :=
  O.qPilotLogVolume = globalQPilotLog (l := l) T

/-- Corrected global link structure (paper qPilot field global). -/
structure S1039GlobalPaperLink where
  source_identifications :
    O.paper_strip_identification ∧
    O.paper_lineBundle_identification ∧
    O.paper_logKummer_identification ∧
    O.paper_qPilot_log_identification
  qPilotLogVolume_eq_paper_global :
    O.qPilotLogVolume = globalQPilotLog (l := l) T
  link_identification : P.procession.average ≤ -O.qPilotLogVolume
  link_implies_inclusion :
    P.procession.average ≤ -O.qPilotLogVolume ->
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

end LeanFormal.IUT.XiFPaper.S1039PaperQFieldAuditActual

end
