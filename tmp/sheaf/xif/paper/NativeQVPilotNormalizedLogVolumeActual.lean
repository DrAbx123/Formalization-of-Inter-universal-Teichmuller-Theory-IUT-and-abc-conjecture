import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual

/-!
# q-pilot normalized scalar from the actual clause-B q_v family

The earlier native q-pilot scalar used the arbitrary
baseQ := badPlaceQCandidate, a Classical.choice of a FinitePlaceQCandidate.
This file replaces that q family by the actual clause-B family

  qVFamily T b = T.clauseB.q_comparison ... .parameter

at the native bad lift.  The local signed/magnitude logs and the Remark 3.1.1
place weights are then applied to this actual family.

This removes one simplification from the xi-f path.  It does not yet construct
the paper's 2l-th root, the LGP presentation, or the Theta hull; no inequality
is asserted.  No sorry, axiom, True, or PUnit is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual clause-B q_v local log-magnitude at a native bad place. -/
noncomputable def nativeQVPilotLocalMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  localLogMagnitude (qVFamily T b)

/-- The actual clause-B q_v local signed log. -/
noncomputable def nativeQVPilotLocalSigned
    (b : Bad (nativePlaceSelection T)) : Real :=
  localSignedLog (qVFamily T b)

/-- The q_v local log-magnitude is positive. -/
theorem nativeQVPilotLocalMagnitude_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < nativeQVPilotLocalMagnitude T b :=
  localLogMagnitude_pos (qVFamily T b)

/-- The signed log is the negative local magnitude. -/
theorem nativeQVPilotLocalSigned_eq_neg
    (b : Bad (nativePlaceSelection T)) :
    nativeQVPilotLocalSigned T b = -nativeQVPilotLocalMagnitude T b :=
  localSignedLog_eq_neg_magnitude (qVFamily T b)

/-- The actual native normalized q-pilot magnitude using the clause-B q_v family
and the actual Remark 3.1.1 place weights. -/
noncomputable def nativeQVPilotNormalizedLogMagnitude : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b

/-- The signed version of the actual q-pilot normalized log-volume. -/
noncomputable def nativeQVPilotNormalizedSignedLogVolume : Real :=
  -nativeQVPilotNormalizedLogMagnitude T

/-- The normalized magnitude is nonnegative. -/
theorem nativeQVPilotNormalizedLogMagnitude_nonneg :
    0 <= nativeQVPilotNormalizedLogMagnitude T := by
  unfold nativeQVPilotNormalizedLogMagnitude
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg
      (localCompletionDegree T.arithmetic (nativeBadToKPlace T b))))
    (le_of_lt (nativeQVPilotLocalMagnitude_pos T b))

/-- Exact formula for the signed scalar. -/
theorem nativeQVPilotNormalizedSignedLogVolume_eq :
    nativeQVPilotNormalizedSignedLogVolume T =
      -∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b :=
  rfl

end LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual

end
