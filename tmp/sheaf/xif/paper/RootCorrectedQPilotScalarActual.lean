import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-!
# Root-corrected q-pilot scalar

The old native qVFamily q-pilot scalar uses

  nativeQVPilotLocalMagnitude b = localLogMagnitude (qVFamily T b),

i.e. the classical q parameter order.  The paper theta value uses the 2l-th
root q_v^(1/2l), whose local logarithmic magnitude is the classical magnitude
divided by 2l.

This file constructs the actual root-corrected local and normalized scalar

  rootLocalMagnitude b = nativeQVPilotLocalMagnitude b / (2l),
  rootNormalizedMagnitude = sum_b w_b * rootLocalMagnitude b,
  rootNormalizedSignedLogVolume = -rootNormalizedMagnitude,

and proves

  nativeQVPilotNormalizedSignedLogVolume T
    = (2*l.value) * rootNormalizedSignedLogVolume T.

The root factor is the actual paper 2l normalization.  The mu_{2l} ambiguity of
the chosen root affects only the root unit, not the local log magnitude; the
scalar formula here uses that invariant magnitude.  No inequality is asserted.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootCorrectedQPilotScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The root-corrected local q_v log-magnitude: classical magnitude / 2l. -/
noncomputable def qVPilotRootLocalMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  nativeQVPilotLocalMagnitude T b / (2 * l.value : Real)

/-- The root-corrected local signed q_v log. -/
noncomputable def qVPilotRootLocalSigned
    (b : Bad (nativePlaceSelection T)) : Real :=
  -qVPilotRootLocalMagnitude T b

/-- The root-corrected normalized q-pilot log-magnitude. -/
noncomputable def qVPilotRootNormalizedMagnitude : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qVPilotRootLocalMagnitude T b

/-- The root-corrected normalized signed q-pilot log-volume. -/
noncomputable def qVPilotRootNormalizedSignedLogVolume : Real :=
  -qVPilotRootNormalizedMagnitude T

/-- The root local magnitude is the old local magnitude divided by 2l. -/
theorem qVPilotRootLocalMagnitude_eq :
    ∀ b : Bad (nativePlaceSelection T),
      qVPilotRootLocalMagnitude T b =
        nativeQVPilotLocalMagnitude T b / (2 * l.value : Real) :=
  fun _ => rfl

/-- The old local magnitude is 2l times the root local magnitude. -/
theorem nativeQVPilotLocalMagnitude_eq_twoL_mul_root
    (b : Bad (nativePlaceSelection T)) :
    nativeQVPilotLocalMagnitude T b =
      (2 * l.value : Real) * qVPilotRootLocalMagnitude T b := by
  unfold qVPilotRootLocalMagnitude
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  exact (mul_div_cancel₀ (nativeQVPilotLocalMagnitude T b) htwo).symm

/-- The root normalized magnitude is the old normalized magnitude divided by
2l. -/
theorem qVPilotRootNormalizedMagnitude_eq :
    qVPilotRootNormalizedMagnitude T =
      nativeQVPilotNormalizedLogMagnitude T / (2 * l.value : Real) := by
  unfold qVPilotRootNormalizedMagnitude
    nativeQVPilotNormalizedLogMagnitude
  calc
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qVPilotRootLocalMagnitude T b)
        = ∑ b : Bad (nativePlaceSelection T),
            (nativeBadLocalWeight T b *
              nativeQVPilotLocalMagnitude T b) / (2 * l.value : Real) := by
          apply Finset.sum_congr rfl
          intro b _
          unfold qVPilotRootLocalMagnitude
          rw [mul_div_assoc]
    _ = (∑ b : Bad (nativePlaceSelection T),
            nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b) /
          (2 * l.value : Real) := by
          rw [Finset.sum_div]

/-- The old normalized magnitude is 2l times the root normalized magnitude. -/
theorem nativeQVPilotNormalizedLogMagnitude_eq_twoL_mul_root :
    nativeQVPilotNormalizedLogMagnitude T =
      (2 * l.value : Real) * qVPilotRootNormalizedMagnitude T := by
  rw [qVPilotRootNormalizedMagnitude_eq]
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  exact (mul_div_cancel₀ (nativeQVPilotNormalizedLogMagnitude T) htwo).symm

/-- The old signed q-pilot scalar is 2l times the root-corrected signed scalar. -/
theorem nativeQVPilotNormalizedSignedLogVolume_eq_twoL_mul_root :
    nativeQVPilotNormalizedSignedLogVolume T =
      (2 * l.value : Real) * qVPilotRootNormalizedSignedLogVolume T := by
  unfold nativeQVPilotNormalizedSignedLogVolume
    qVPilotRootNormalizedSignedLogVolume
  rw [nativeQVPilotNormalizedLogMagnitude_eq_twoL_mul_root]
  ring

/-- Exact formula for the root-corrected normalized magnitude. -/
theorem qVPilotRootNormalizedMagnitude_eq_weighted :
    qVPilotRootNormalizedMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (nativeQVPilotLocalMagnitude T b / (2 * l.value : Real)) := by
  unfold qVPilotRootNormalizedMagnitude qVPilotRootLocalMagnitude
  rfl


-- The paper coefficient assignment, written explicitly to prevent confusing
-- the classical q-pilot scalar with the root-normalized auxiliary scalar.

/-- The paper q-pilot coefficient n_b = ord(qVFamily). -/
noncomputable def qPilotPaperCoefficient (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).order : Real)

/-- The paper Theta coefficient j^2 * n_b/(2l). -/
noncomputable def thetaPaperCoefficient
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  ((gaussExponent j.1).toNat : Real) * qVFamPaperRootCoefficient T b

/-- The auxiliary root-normalized q coefficient n_b/(2l). This is not the
paper q-pilot coefficient. -/
noncomputable def rootQAuxiliaryCoefficient
    (b : Bad (nativePlaceSelection T)) : Real :=
  qVFamPaperRootCoefficient T b

end LeanFormal.IUT.XiFPaper.RootCorrectedQPilotScalarActual

end
