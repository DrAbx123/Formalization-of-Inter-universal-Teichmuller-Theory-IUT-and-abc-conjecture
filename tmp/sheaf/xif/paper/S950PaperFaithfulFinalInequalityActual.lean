import tmp.sheaf.xif.paper.S942ActualPaperSInterfaceActual
import tmp.sheaf.xif.paper.S946QPilotCarrierAuditActual

-- S950: final paper-faithful inequality, conditional on:
-- actual paper D + Ind nonempty/bounded (S942), carrier bridge (S946),
-- and paper qPilot log <= model R log.
-- No theta-only/empty substitution, no equality/scaling data.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S950PaperFaithfulFinalInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S942ActualPaperSInterfaceActual
open LeanFormal.IUT.XiFPaper.S946QPilotCarrierAuditActual
open LeanFormal.IUT.XiFPaper.S926GlobalIntegrationActual
open MeasureTheory

universe ua uv upi umon ui uG uX u

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uX} {Choice : Type uX} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable (O : PaperQPilotObject (l := l) (V := V)
  (Label := Label) (Choice := Choice) I G envStrip)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- Exact minimal data for the final paper-faithful inequality. -/
structure PaperFaithfulFinalData where
  bridge : ∀ b : Bad (nativePlaceSelection T),
    PaperQPilotCarrierBridge (T := T) b
  sInterface : ActualPaperSInterface T mu
  paperLog_le_modelLog :
    O.qPilotLogVolume ≤ globalModelLog (l := l) T mu

/-- Final paper-faithful inequality: paper qPilot log <= paperSHull log. -/
def PaperFaithfulFinalInequality
    (H : PaperFaithfulFinalData (l := l) (T := T) O mu) : Prop :=
  O.qPilotLogVolume ≤
    globalPaperSLog (l := l) T mu H.sInterface.D

theorem paperFaithfulFinalInequality
    (H : PaperFaithfulFinalData (l := l) (T := T) O mu) :
    PaperFaithfulFinalInequality (l := l) O T mu H :=
  le_trans H.paperLog_le_modelLog H.sInterface.global_le

/-- Exact carrier bridge obligation for all bad places. -/
def S950CarrierBridgeRequired : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    Nonempty (PaperQPilotCarrierBridge (T := T) b)

theorem paperFaithfulFinalInequality_of_data
    (bridge : S950CarrierBridgeRequired (T := T))
    (sInterface : ActualPaperSInterface T mu)
    (hlog : O.qPilotLogVolume ≤ globalModelLog (l := l) T mu) :
    O.qPilotLogVolume ≤ globalPaperSLog (l := l) T mu sInterface.D :=
  le_trans hlog sInterface.global_le

#check paperFaithfulFinalInequality
#check PaperFaithfulFinalData
#check S950CarrierBridgeRequired

end LeanFormal.IUT.XiFPaper.S950PaperFaithfulFinalInequalityActual

end