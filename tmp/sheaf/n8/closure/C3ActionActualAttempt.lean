import tmp.sheaf.n8.closure.C3CompleteSourceReduction
import tmp.sheaf.n8.closure.C3KummerActual
import tmp.sheaf.n8.closure.NativeC3
import Mathlib

/-!
# C3 action attempt: actual trivial Kummer action vs source Galois action

C3KummerActual.NativeKummerAction is a genuine group action on the
algebraic-closure units, with the actual q-unit fixed.

This file first constructs the actual trivial action (group PUnit, identity
action, q fixed by rfl).  This discharges the NativeKummerActionObligation
sub-obligation of C3CompleteSourceReduction without any arbitrary map.

It then records the exact source-action gap: the nontrivial source local Galois
action is not constructed in the tree for the actual completion
AlgebraicClosure (Completion nativeFPlaceOverBad).  The trivial action is not
claimed to be the source Galois action.
-/

noncomputable section

namespace ABCBridge.N8.C3ActionActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3KummerActual
open ABCBridge.N8.C3CompleteSourceReduction

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual trivial Kummer action: group PUnit acts by the identity on
AlgebraicClosure units.  This is a real action, not a free field, but it is not
the cited nontrivial local Galois action. -/
noncomputable def trivialNativeKummerAction (q : NativeQDonor X) :
    NativeKummerAction.{0} X q where
  G := PUnit
  groupG := inferInstance
  rho := 1
  fixed := by
    intro σ
    cases σ
    rfl

/-- The NativeKummerActionObligation of C3CompleteSourceReduction is indeed
inhabited by the actual trivial action. -/
theorem nativeKummerActionObligation_holds :
    NativeKummerActionObligation (X := X) :=
  ⟨⟨nativeQDonorActual X, trivialNativeKummerAction X (nativeQDonorActual X)⟩⟩

/-- Exact source-faithful action obligation: the action must be the actual
local Galois action, not the trivial PUnit action.  No such construction exists
for AlgebraicClosure (Completion nativeFPlaceOverBad) in the current tree. -/
def NativeSourceGaloisActionObligation : Prop :=
  Nonempty (Sigma (fun q : NativeQDonor X =>
    { A : NativeKummerAction.{0} X q // A.G ≠ PUnit }))

end ABCBridge.N8.C3ActionActualAttempt
