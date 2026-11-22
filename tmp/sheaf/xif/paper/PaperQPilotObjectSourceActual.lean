import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-! # PaperQPilotObject from actual source data

This file constructs an actual PaperQPilotObject whose data fields are built
from actual source objects:

* boundary : an actual SourceProcessionBoundary.Input;
* strip := sourceQPilotStrip boundary (definitionally);
* oneColumn : an actual SourceOneColumnArithmeticHolomorphicStructure;
* lineBundle : an actual SourceArithmeticVectorBundle over that oneColumn;
* logKummer : an actual SourceKummerArrow envStrip strip;
* qPilotLogVolume := sourceQPilotSignedLog I.initial (actual source scalar).

The four paper_*_identification fields are NOT set to True/PUnit.  The paper
targets for the strip/line bundle/log-Kummer/q-log identification are not
present as types in the frozen source; this file records that exact type
obstruction by four empty target types and the corresponding Nonempty
propositions.  No equality to a nonexistent paper target is fabricated.
No toy/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT
namespace Theorem311Source

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui uG uL uC

/-- The paper q-pilot F-prime-strip target type is not present in the frozen source. -/
inductive MissingPaperQPilotStripTarget : Type

/-- The paper rank-one arithmetic line bundle target type is not present. -/
inductive MissingPaperLineBundleTarget : Type

/-- The paper log-Kummer representation target type on 1,circ U_Q is not present. -/
inductive MissingPaperLogKummerTarget : Type

/-- The paper procession-normalized q-pilot log-volume target type is not present. -/
inductive MissingPaperQPilotLogTarget : Type

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}

/-- Actual PaperQPilotObject constructed from actual source boundary, one-column
structure, arithmetic vector bundle, Kummer arrow, and source q-pilot scalar.
The four identification fields are explicit empty-target type obstructions, not
True/PUnit. -/
noncomputable def paperQPilotObjectSourceActual
    (boundary : LeanFormal.IUT.SourceProcessionBoundary.Input
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    (lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))
    (logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip where
  boundary := boundary
  strip := sourceQPilotStrip boundary
  strip_eq_source := rfl
  oneColumn := oneColumn
  lineBundle := lineBundle
  logKummer := logKummer
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification := Nonempty MissingPaperQPilotStripTarget
  paper_lineBundle_identification := Nonempty MissingPaperLineBundleTarget
  paper_logKummer_identification := Nonempty MissingPaperLogKummerTarget
  paper_qPilot_log_identification := Nonempty MissingPaperQPilotLogTarget

/-- The boundary field is the actual supplied source boundary. -/
theorem paperQPilotObjectSourceActual_boundary
    (boundary : LeanFormal.IUT.SourceProcessionBoundary.Input
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    (lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))
    (logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) :
    (paperQPilotObjectSourceActual (I := I) (G := G)
      (envStrip := envStrip) boundary oneColumn lineBundle logKummer).boundary =
      boundary := rfl

/-- The strip field is exactly the actual source q-pilot strip anchor. -/
theorem paperQPilotObjectSourceActual_strip
    (boundary : LeanFormal.IUT.SourceProcessionBoundary.Input
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    (lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))
    (logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) :
    (paperQPilotObjectSourceActual (I := I) (G := G)
      (envStrip := envStrip) boundary oneColumn lineBundle logKummer).strip =
      sourceQPilotStrip boundary := rfl

/-- The q-pilot log-volume field is the actual source q-pilot scalar. -/
theorem paperQPilotObjectSourceActual_qPilotLogVolume
    (boundary : LeanFormal.IUT.SourceProcessionBoundary.Input
      (l := l) (V := V) (Label := Label) (Choice := Choice))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    (lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))
    (logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) :
    (paperQPilotObjectSourceActual (I := I) (G := G)
      (envStrip := envStrip) boundary oneColumn lineBundle logKummer).qPilotLogVolume =
      sourceQPilotSignedLog I.initial := rfl

end Theorem311Source
end LeanFormal.IUT

end
