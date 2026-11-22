import tmp.sheaf.n8.closure.PaperP6ComparisonActual
import tmp.sheaf.n8.closure.C9Paper

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# Paper P6 conclusion and exact C9 volume bridge

PaperP6Conclusion is the proved paper-level inequality
log ||q|| <= thetaLogVolume.

C9Paper's QPaper/ThetaPaper carry their own C3/C1/C2/C6 provenance and their
own qPilotLogVolume/thetaLogVolume.  The exact bridge is a pair of provenance
equalities.  No production construction of those equalities from an arbitrary
SourceInitialThetaData exists; the gap is recorded as C9BridgeGap, not assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperP6ToC9

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive}

abbrev PaperKf (S : SourceInitialThetaData l) : Type :=
  CommonPrimeCompletion (placeAtPrime S)

/-- Paper-level C7 conclusion: log||q|| is at most the normalized hull
log-volume. -/
def PaperP6Conclusion (S : SourceInitialThetaData l) : Prop :=
  Real.log ‖((qUnit S : (C7MassFormulaZeroSorry.PaperKf S)ˣ) : C7MassFormulaZeroSorry.PaperKf S)‖ ≤ thetaLogVolume S

theorem paperP6Conclusion_actual (S : SourceInitialThetaData l) :
    PaperP6Conclusion S := by
  unfold PaperP6Conclusion
  exact paper_log_norm_le_thetaLogVolume S

/-- Exact volume-level bridge data: Q and Theta carry the two paper log-volumes,
with equalities to the proved paper quantities. -/
structure C9VolumeBridge (S : SourceInitialThetaData l) where
  qVolume : WithTop Real
  thetaVolume : WithTop Real
  qVolume_eq : qVolume = (Real.log ‖(qUnit S : PaperKf S)‖ : WithTop Real)
  thetaVolume_eq : thetaVolume = (thetaLogVolume S : WithTop Real)

/-- Conditional C9 inequality from the exact volume bridge. -/
theorem c9_q_le_theta_of_volumeBridge
    (S : SourceInitialThetaData l) (B : C9VolumeBridge S) :
    B.qVolume ≤ B.thetaVolume := by
  rw [B.qVolume_eq, B.thetaVolume_eq]
  exact_mod_cast paperP6Conclusion_actual S

/-- Exact bridge gap at the volume level: no production C9Paper Q/Theta
provenance gives these two equalities from the paper source. -/
def C9BridgeGap (S : SourceInitialThetaData l) : Prop :=
  ¬ Nonempty (C9VolumeBridge S)


/-- The volume-level bridge is actually inhabited: it only pins the two paper
log-volumes.  The old C9BridgeGap proposition is therefore false; the real
gap is provenance (C9Paper Q/Theta definitions), not volume existence. -/
noncomputable def c9VolumeBridge_actual (S : SourceInitialThetaData l) :
    C9VolumeBridge S where
  qVolume := (Real.log ‖(qUnit S : PaperKf S)‖ : WithTop Real)
  thetaVolume := (thetaLogVolume S : WithTop Real)
  qVolume_eq := rfl
  thetaVolume_eq := rfl

theorem c9VolumeBridge_nonempty (S : SourceInitialThetaData l) :
    Nonempty (C9VolumeBridge S) :=
  ⟨c9VolumeBridge_actual S⟩

theorem c9BridgeGap_false (S : SourceInitialThetaData l) :
    ¬ C9BridgeGap S :=
  fun h => h (c9VolumeBridge_nonempty S)

end LeanFormal.IUT.N8Closure.PaperP6ToC9

end