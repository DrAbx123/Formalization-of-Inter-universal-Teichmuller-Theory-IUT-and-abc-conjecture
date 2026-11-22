import tmp.sheaf.n8.closure.SourceValues
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false

/-!
# C9 native: actual q-region/theta-hull signed Values

Q is the actual q-region signed log `sourceSignedImageLogVolume`; Theta is the
actual theta-hull signed log `sourceSignedHullLogVolume`; Values is the set of
actual C4 witnessed-output values read through `sourceLocalLogDegree` and
signed.  The old C9IQ singleton Values / iqSignedHullLog is not used.

The native comparison theorem is not asserted: the only production direction
is `sourceSignedHullLogVolume <= sourceSignedImageLogVolume` (hull contained
in image-union), while C9 needs the source comparison
`QSigned <= ThetaSigned`.  The exact missing declaration is recorded below.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceValues

namespace LeanFormal.IUT.N8Closure.C9Native

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {Label : Type uL} [Group Label]
  (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- Actual q-region signed log `-|log(q)|` from the production donor. -/
def QSigned (n : ThetaPilotCarrier l) : ℝ :=
  I.sourceSignedImageLogVolume D.place.v D.place.R n

/-- Actual theta-hull signed log `-|log(Theta)|` from the production donor. -/
def ThetaSigned (n : ThetaPilotCarrier l) : ℝ :=
  I.sourceSignedHullLogVolume D.place.v D.place.R n

/-- Actual allowed output values: the C4 witnessed output log-degrees, signed. -/
def Values (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) : Set ℝ :=
  {z | ∃ y ∈ SourceValues.values (D := D) n x, z = -y}

/-- Native value bound: every actual signed output value is at most Theta. -/
def ActualValuesBounded : Prop :=
  ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
    (z : ℝ), z ∈ Values (D := D) n x → z ≤ ThetaSigned (D := D) n

/-- Native q approximation: every q-region signed log is approximated from
below by an actual allowed output value. -/
def ActualQApproximated : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) (z : ℝ),
      z ∈ Values (D := D) n x ∧ QSigned (D := D) n - ε ≤ z

/-- Exact missing source donor: the signed q/hull comparison for every
procession.  Production proves only the reverse direction from hull
containment; this is the C9 (xi-f) comparison, not a free hypothesis. -/
def MissingSourceQHullComparison : Prop :=
  ∀ n : ThetaPilotCarrier l, QSigned (D := D) n ≤ ThetaSigned (D := D) n

/-- Exact missing value/Θ relation: the actual signed output values are
bounded by the theta-hull signed log.  No production lemma currently gives
this direction for the full C4 witnessed choice family. -/
def MissingValuesBoundedByTheta : Prop :=
  ActualValuesBounded (D := D)

theorem actual_values_bounded_of_missing (h : MissingValuesBoundedByTheta (D := D)) :
    ActualValuesBounded (D := D) := h

end LeanFormal.IUT.N8Closure.C9Native

end
