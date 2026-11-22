import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.SourcePilotApproximationIQ

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false

/-!
# C9 actual q-pilot Real readout

Defines the actual source q-pilot Real readout `-log ||C3.q.q||` in the
completion.  This file deliberately does NOT assert the donor identity with
the C8 signed hull: C8's signed hull is `B.signedHullLog` on the canonical
hull and is independent of `C3.q`; no C3/C7/C8 field relates them.

Stage-3 status: exact no-go for `sourcePilotApproximationIQ_stage2` as an
actual q comparison.  See C9-STAGE3.md.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion

namespace LeanFormal.IUT.N8Closure.C9Actual

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {LAdd : Type uG} [AddGroup LAdd]

variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual source q-pilot Real readout: `-log ||q||` in the finite-place
completion.  This is the actual q value of C3, not a free Real field. -/
noncomputable def actualQPilotRealReadout : ℝ :=
  -Real.log ‖(C3.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)‖

theorem actualQPilotRealReadout_eq :
    actualQPilotRealReadout (I := I) C3 =
      -Real.log ‖(C3.q.q : CommonPrimeCompletion
        (K := I.initial.arithmetic.Fmod) C3.place)‖ := rfl

end LeanFormal.IUT.N8Closure.C9Actual

end
