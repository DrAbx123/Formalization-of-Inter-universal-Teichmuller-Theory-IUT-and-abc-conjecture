import tmp.sheaf.xif.paper.S21bCompletionThetaNormBridgeActual
import tmp.sheaf.xif.paper.PaperSourceThetaConsistencyActual

/-! # S21c: actual source qUnit construction for the norm bridge

PaperSourceThetaConsistencyActual constructs the actual qVFamily completion unit
sourceQVFamilyUnit and the actual theta packet sourceThetaPacketFromQ with

  sourceThetaPacketFromQ.q = ||sourceQVFamilyUnit||.

Therefore the completion unit and the packet have an actual norm/scale bridge
without any extra qUnit/hq input.  For the source theater theta packet, the
exact condition is equality of the theater packet q with sourceThetaQ; under
that exact correction condition the S21 CompletionThetaNormBridge is obtained
from the actual qVFamily unit.

No fake equality; the mismatch condition is recorded exactly.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S21cActualQUnitBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.S21bCompletionThetaNormBridgeActual
open LeanFormal.IUT.XiFPaper.S21DegreeNormAlignmentActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (n : ThetaPilotCarrier l)

/-- Actual qVFamily completion unit at the source theta place. -/
noncomputable abbrev actualS21QUnit : (CommonPrimeCompletion (sourceThetaPlace T b))ˣ :=
  sourceQVFamilyUnit T b

/-- Actual theta packet constructed from the qVFamily norm. -/
noncomputable abbrev actualS21ThetaPacket : FiniteThetaPacket l :=
  sourceThetaPacketFromQ (l := l) T b

/-- Actual norm equality of the source q unit and the constructed packet q. -/
theorem actualS21QUnit_norm :
    ‖(actualS21QUnit (l := l) T b : CommonPrimeCompletion (sourceThetaPlace T b))‖ =
      (actualS21ThetaPacket (l := l) T b).q := rfl

/-- The constructed packet scale at label 1 is the q norm. -/
theorem actualS21ThetaPacket_scale_one :
    (actualS21ThetaPacket (l := l) T b).scale (oneLabel l) =
      (actualS21ThetaPacket (l := l) T b).q := by
  rw [(actualS21ThetaPacket (l := l) T b).scale_eq]
  simp [oneLabel, realThetaValue, gaussExponent]

/-- Actual completion-unit/norm scale bridge for the constructed source packet:
no extra qUnit/hq input. -/
theorem actualConstructedCompletionThetaBridge :
    ∃ u : (CommonPrimeCompletion (sourceThetaPlace T b))ˣ,
      0 < ‖(u : CommonPrimeCompletion (sourceThetaPlace T b))‖ ∧
        Real.log ‖(u : CommonPrimeCompletion (sourceThetaPlace T b))‖ =
          Real.log ((actualS21ThetaPacket (l := l) T b).scale (oneLabel l)) := by
  refine ⟨actualS21QUnit (l := l) T b, ?_, ?_⟩
  · exact norm_pos_iff.mpr (Units.ne_zero _)
  · rw [actualS21QUnit_norm, ← actualS21ThetaPacket_scale_one (l := l) T b]

/-- Actual source bridge for the constructed source packet (no qUnit/hq input). -/
def ActualSourceCompletionThetaNormBridge : Prop :=
  ∃ u : (CommonPrimeCompletion (sourceThetaPlace T b))ˣ,
    0 < ‖(u : CommonPrimeCompletion (sourceThetaPlace T b))‖ ∧
      Real.log ‖(u : CommonPrimeCompletion (sourceThetaPlace T b))‖ =
        Real.log ((actualS21ThetaPacket (l := l) T b).scale (oneLabel l))

theorem actualSourceCompletionThetaNormBridge_holds :
    ActualSourceCompletionThetaNormBridge (l := l) T b :=
  actualConstructedCompletionThetaBridge (l := l) T b

/-- Exact correction condition for the source theater packet q. -/
def SourceTheaterQCorrection : Prop :=
  (I.theaterAt (n.val : Int) 0).thetaPacket.q =
    sourceThetaQ T b

/-- Exact field/place correction condition needed to read the qVFamily F-place
as the source theater Fmod place in the S21 bridge. -/
def SourceTheaterFieldCorrection : Prop :=
  T.arithmetic.F = I.initial.arithmetic.Fmod

/-- Exact mismatch/root correction gap for the source theater packet. -/
def SourceTheaterQCorrectionRequired
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) : Prop :=
  SourceTheaterQCorrection (l := l) T b n (I := I) ∧
    SourceTheaterFieldCorrection (l := l) T (I := I)

end LeanFormal.IUT.XiFPaper.S21cActualQUnitBridgeActual

end
