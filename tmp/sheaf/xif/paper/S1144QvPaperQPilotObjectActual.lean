import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperLineBundleCarrierActual

/-! # S1144: q_v collection -> PaperQPilotObject (actual construction + exact line-bundle gap)

PaperQPilotObject requires actual source data (boundary, oneColumn, logKummer)
and a line-bundle carrier, plus four identification Props (stored, not proved).
The q_v collection enters through the actual scalar
sourceQPilotSignedLog I.initial = -sum_b |log q_b|; the structure field
qPilotLogVolume_eq is then rfl.

We construct the object actual from that source data.  The line-bundle carrier
is the honest pole-allowing completion carrier (all finite-place completion
sections, localization = evaluation); no arbitrary data is invented.

The bad-place/line-bundle identification itself remains exact: badPlaces has no
map to finite places in I.initial, and the carrier does not encode q_v sections.
That is recorded as S1144BadPlaceLineBundleIdentificationRequired.-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1144QvPaperQPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open MeasureTheory

universe ua uv upi umon ui uG uL uC

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}

/-- Actual q_v data plus the remaining source datum needed by the paper object.
The four identification Props are stored exactly; none is asserted. -/
structure S1144QvSourceData where
  boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
    (l := l) (V := V) (Label := Label) (Choice := Choice)
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)
  paper_strip_identification : Prop
  paper_lineBundle_identification : Prop
  paper_logKummer_identification : Prop
  paper_qPilot_log_identification : Prop

/-- Actual pole-allowing line-bundle carrier: all finite-place completion
sections, localization by evaluation. -/
noncomputable def s1144LineBundle :
    PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod) where
  total := (v : NumberField.FinitePlace I.initial.arithmetic.Fmod) →
    Completion v
  localization := fun v f => f v

/-- The paper QPilotObject constructed from the q_v/source data actual. -/
noncomputable def s1144PaperQPilotObject
    (D : S1144QvSourceData (l := l) (V := V) (G := G) (envStrip := envStrip)) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip where
  boundary := D.boundary
  strip := sourceQPilotStrip D.boundary
  strip_eq_source := rfl
  oneColumn := D.oneColumn
  lineBundle := s1144LineBundle (l := l) (V := V) (I := I)
  logKummer := D.logKummer
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification := D.paper_strip_identification
  paper_lineBundle_identification := D.paper_lineBundle_identification
  paper_logKummer_identification := D.paper_logKummer_identification
  paper_qPilot_log_identification := D.paper_qPilot_log_identification

/-- The constructed qPilotLogVolume is the q_v absolute-log sum. -/
theorem s1144PaperQPilotObject_qPilotLogVolume
    (D : S1144QvSourceData (l := l) (V := V) (G := G) (envStrip := envStrip)) :
    (s1144PaperQPilotObject (l := l) (V := V) (G := G) (envStrip := envStrip) D).qPilotLogVolume =
      -∑ b : I.initial.badPlaces, |Real.log (I.initial.reduction.qParameter b)| := rfl

/-- Exact missing bad-place -> finite-place map for the paper line-bundle
identification. -/
def S1144BadPlaceToFinitePlace : Prop :=
  Nonempty (I.initial.badPlaces → NumberField.FinitePlace I.initial.arithmetic.Fmod)

/-- Exact remaining line-bundle identification obligation. -/
def S1144BadPlaceLineBundleIdentificationRequired : Prop :=
  S1144BadPlaceToFinitePlace (I := I) ∧
    Nonempty (PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))

end LeanFormal.IUT.XiFPaper.S1144QvPaperQPilotObjectActual

end
