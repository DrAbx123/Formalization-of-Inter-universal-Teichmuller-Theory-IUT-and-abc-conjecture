import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.C9QThetaValuesNamed

/-!
# P6 GlobalLqDonor underconstrained (Wave20)

GlobalLqDonor is only a function on P6ChainALocal plus one equality at the
distinguished point p6ChainALocal X.  It contains no source global L_q data.

Therefore the constant readout is an actual inhabitant:

  readout := fun _ => qPilotSignedLog X
  readout_eq_local := rfl

This decisively corrects the target: Nonempty (GlobalLqDonor X) and
C9QThetaValuesNamed.MissingQSource are vacuous formal inhabitants, not evidence
of the source global L.  They must not be used as a Q-source proof.  The
dependents of Z6/P6ChainA.globalLqDonor_nonempty should use
globalLqDonor_nonempty_actual only as the formal readout interface, and must not
claim source global L existence.

No owner file is edited and no new free field is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6GlobalLqDonorUnderconstrained

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Constant formal readout donor.  Only the distinguished-point equality is
checked; this is not the source global L_q realization. -/
def constantGlobalLqDonor : GlobalLqDonor X where
  readout := fun _ => C9QPilotRegion.qPilotSignedLog X
  readout_eq_local := rfl

/-- Its L_q value is the local q-pilot scalar. -/
theorem constantGlobalLqDonor_Lq :
    Lq X (constantGlobalLqDonor X) = C9QPilotRegion.qPilotSignedLog X :=
  rfl

/-- Actual existence of the formal donor interface. -/
theorem globalLqDonor_nonempty_actual : Nonempty (GlobalLqDonor X) :=
  ⟨constantGlobalLqDonor X⟩

/-- Decisive target correction: MissingQSource is exactly the formal donor
existence, hence inhabited by the constant readout.  It does not assert source
global L. -/
theorem missingQSource_actual : MissingQSource X :=
  globalLqDonor_nonempty_actual X

/-- The constant donor gives a formal Chain A; its Q is the native q scalar. -/
def constantChainA : P6ChainAData X :=
  p6ChainAOfGlobalLq X (constantGlobalLqDonor X)

theorem constantChainA_Q :
    (constantChainA X).Q = C9QPilotRegion.qPilotSignedLog X := by
  change Lq X (constantGlobalLqDonor X) = C9QPilotRegion.qPilotSignedLog X
  rfl

/-- Exact target correction record: the formal donor does not supply any source
global L witness; only the readout interface and its one-point equality. -/
def FormalOnlyGlobalLqDonor (D : GlobalLqDonor X) : Prop :=
  D.readout (p6ChainALocal X) = C9QPilotRegion.qPilotSignedLog X

theorem constantGlobalLqDonor_formalOnly :
    FormalOnlyGlobalLqDonor X (constantGlobalLqDonor X) :=
  rfl

end LeanFormal.IUT.N8Closure.P6GlobalLqDonorUnderconstrained
