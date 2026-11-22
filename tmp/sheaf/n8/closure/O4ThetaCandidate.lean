import tmp.sheaf.n8.closure.C9Native
import tmp.sheaf.n8.closure.C9Paper
import tmp.sheaf.n8.closure.EtaGlobalQOReadoutCanonical
import Mathlib

/-!
# O4 Theta/Values candidate actual

Source-facing O4 branch: the actual Theta candidate is the production
sourceSignedHullLogVolume, and the actual Values candidate is the production
C4 witnessed-output signed value set.  These are source objects, not new
local readouts.  The paper ellOut Theta needs an actual P6Readout/source
output-region witness, which is not constructed.  The needed Q <= Theta
direction is C9Native.MissingSourceQHullComparison; production proves only
the reverse hull-containment direction.  No arbitrary object is introduced.
-/

noncomputable section

set_option maxHeartbeats 800000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceValues
open LeanFormal.IUT.N8Closure.C9Native

namespace LeanFormal.IUT.N8Closure.O4ThetaCandidate

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {Label : Type uL} [Group Label]
  (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- Actual source Theta candidate: the production theta-hull signed log. -/
noncomputable def ActualThetaCandidate (n : ThetaPilotCarrier l) : ℝ :=
  I.sourceSignedHullLogVolume D.place.v D.place.R n

/-- Actual source Q candidate: the production q-region signed log. -/
noncomputable def ActualQCandidate (n : ThetaPilotCarrier l) : ℝ :=
  I.sourceSignedImageLogVolume D.place.v D.place.R n

/-- Actual source Values candidate: the C4 witnessed-output signed values. -/
noncomputable def ActualValuesCandidate (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) : Set ℝ :=
  C9Native.Values (D := D) n x

/-- Actual source ValuesBounded candidate. -/
def ActualValuesBoundedCandidate : Prop :=
  ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) (z : ℝ),
    z ∈ ActualValuesCandidate (D := D) n x → z ≤ ActualThetaCandidate (D := D) n

/-- Exact Q <= Theta source direction. -/
def ActualQLeThetaCandidate : Prop :=
  ∀ n : ThetaPilotCarrier l,
    ActualQCandidate (D := D) n ≤ ActualThetaCandidate (D := D) n

theorem actualQLeThetaCandidate_iff_missing :
    ActualQLeThetaCandidate (D := D) ↔
      C9Native.MissingSourceQHullComparison (D := D) := Iff.rfl

theorem actualValuesBoundedCandidate_iff_missing :
    ActualValuesBoundedCandidate (D := D) ↔
      C9Native.MissingValuesBoundedByTheta (D := D) := Iff.rfl

/-- Exact O4 source data; not asserted. -/
structure O4SourceThetaData : Prop where
  qLeTheta : ActualQLeThetaCandidate (D := D)
  valuesBounded : ActualValuesBoundedCandidate (D := D)

end LeanFormal.IUT.N8Closure.O4ThetaCandidate