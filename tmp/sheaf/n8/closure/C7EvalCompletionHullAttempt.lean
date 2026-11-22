import tmp.sheaf.n8.closure.C7U2IQSourceAttempt
import tmp.sheaf.n8.closure.C7Reductions
import Mathlib

/-!
# C7 eval-completion hull attempt

For an EvalToCompletionDonor M, the canonical-hull condition on sourceU is
exactly pointwise theta-image containment: every sourceU element is an actual
C4 eval, and on evals C3.tensorLanding ∘ M.evalToCompletion equals T.thetaImage.
Thus the hull condition reduces to ThetaImageContainmentDonor and cannot be
proved from the donor alone.  The source paper hull is on a different carrier,
so it is not used as a canonical-hull membership proof.

One named gap remains: theta-image containment.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7EvalCompletionHullAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7SourceU
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7Reductions
open LeanFormal.IUT.N8Closure.C7U2IQSourceAttempt

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- The canonical-hull condition for an eval-to-completion donor is exactly
pointwise theta-image containment. -/
theorem evalToCompletionHullCondition_iff_thetaContainment
    (M : EvalToCompletionDonor (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :
    EvalToCompletionHullCondition (C3 := C3) (D := D) (T := T) (n := n) (x := x) M ↔
      ThetaImageContainmentDonor (C3 := C3) T n := by
  constructor
  · intro h c
    have hc : D.eval n x c ∈ sourceU (D := D) n x := ⟨c, rfl⟩
    simpa [M.eval_theta_compat c] using h (D.eval n x c) hc
  · intro h y hy
    rcases hy with ⟨c, rfl⟩
    rw [M.eval_theta_compat c]
    exact h c

/-- The source U is contained in the actual source holomorphic hull. -/
theorem sourceU_subset_sourceHull :
    sourceU (D := D) n x ⊆
      I.sourceHolomorphicHull D.place.v D.place.R n :=
  LeanFormal.IUT.N8Closure.C7SourceU.sourceU_subset_sourceHolomorphicHull
    (D := D) n x

/-- Conditional hull condition from the exact theta donor. -/
theorem evalToCompletionHullCondition_of_thetaDonor
    (M : EvalToCompletionDonor (C3 := C3) (D := D) (T := T) (n := n) (x := x))
    (h : ThetaImageContainmentDonor (C3 := C3) T n) :
    EvalToCompletionHullCondition (C3 := C3) (D := D) (T := T) (n := n) (x := x) M :=
  (evalToCompletionHullCondition_iff_thetaContainment (C3 := C3) (D := D)
    (T := T) (n := n) (x := x) M).mpr h

/-- The hull condition holds for every donor once theta containment is known. -/
theorem evalToCompletionHullCondition_exists
    (h : ThetaImageContainmentDonor (C3 := C3) T n)
    (M : EvalToCompletionDonor (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :
    EvalToCompletionHullCondition (C3 := C3) (D := D) (T := T) (n := n) (x := x) M :=
  evalToCompletionHullCondition_of_thetaDonor (C3 := C3) (D := D) (T := T)
    (n := n) (x := x) M h

end LeanFormal.IUT.N8Closure.C7EvalCompletionHullAttempt
