import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

/-!
# Actual source output values

The numeric images of the actual C4 witnessed output, read through the
source local log-degree.  The witness is retained by an existential over the
actual choice `c`; this is not a free set of reals.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceValues

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- The actual numeric output values at `(n,x)`: images of the actual
source evaluation over the actual choice family, retaining witnesses. -/
def values (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) : Set ℝ :=
  {y | ∃ c : D.Choice n x, I.sourceLocalLogDegree D.place.v (D.eval n x c) = y}

theorem mem_values_iff (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
    (y : ℝ) :
    y ∈ values (D := D) n x ↔
      ∃ c : D.Choice n x, I.sourceLocalLogDegree D.place.v (D.eval n x c) = y :=
  Iff.rfl

theorem values_nonempty (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    (values (D := D) n x).Nonempty := by
  refine ⟨I.sourceLocalLogDegree D.place.v (D.eval n x zeroSignedLabel), ?_⟩
  exact ⟨zeroSignedLabel, rfl⟩

theorem values_finite (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) :
    (values (D := D) n x).Finite := by
  unfold values
  exact Set.finite_range (fun c : D.Choice n x =>
    I.sourceLocalLogDegree D.place.v (D.eval n x c))

end LeanFormal.IUT.N8Closure.SourceValues