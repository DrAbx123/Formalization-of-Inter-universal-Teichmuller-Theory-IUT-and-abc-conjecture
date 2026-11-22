import tmp.sheaf.xif.paper.RootCorrectedQPilotScalarActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual

/-! # Final q-pilot/Theta-root scalar inequality

We do NOT unify the two coefficients.  They remain separate actual formulas:

* q-pilot classical local magnitude:
    qPilotClassicalLocalMagnitude b = nativeQVPilotLocalMagnitude T b;
* theta root local magnitude:
    thetaRootLocalMagnitude b = nativeQVPilotLocalMagnitude T b / (2l).

The corresponding global normalized magnitudes are the native qVFamily
normalized magnitude and the root-corrected normalized magnitude.  Since the
classical magnitude is nonnegative and 2l >= 1, the root magnitude is at most
the classical magnitude.  This gives the final positive inequality and its
signed form; no coefficient unification is used.

No fake inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotThetaFinalInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.RootCorrectedQPilotScalarActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- q-pilot classical local magnitude, separate actual formula. -/
noncomputable def qPilotClassicalLocalMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  nativeQVPilotLocalMagnitude T b

/-- Theta root local magnitude, separate actual formula. -/
noncomputable def thetaRootLocalMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  nativeQVPilotLocalMagnitude T b / (2 * l.value : Real)

/-- Actual local inequality: theta root magnitude <= q-pilot classical
magnitude. -/
theorem thetaRootLocalMagnitude_le_qPilotClassical
    (b : Bad (nativePlaceSelection T)) :
    thetaRootLocalMagnitude T b ≤ qPilotClassicalLocalMagnitude T b := by
  unfold thetaRootLocalMagnitude qPilotClassicalLocalMagnitude
  have hq : 0 ≤ nativeQVPilotLocalMagnitude T b :=
    le_of_lt (nativeQVPilotLocalMagnitude_pos T b)
  have hl : (1 : Real) ≤ (2 * l.value : Real) := by
    have hpos : 0 < l.value := l.prime.pos
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) hpos))
  calc
    nativeQVPilotLocalMagnitude T b / (2 * l.value : Real)
        ≤ nativeQVPilotLocalMagnitude T b / 1 :=
          div_le_div_of_nonneg_left hq zero_lt_one hl
    _ = nativeQVPilotLocalMagnitude T b := div_one _

/-- q-pilot classical normalized magnitude, separate actual formula. -/
noncomputable def qPilotClassicalNormalizedMagnitude : Real :=
  nativeQVPilotNormalizedLogMagnitude T

/-- Theta root normalized magnitude, separate actual formula. -/
noncomputable def thetaRootNormalizedMagnitude : Real :=
  qVPilotRootNormalizedMagnitude T

/-- The root normalized magnitude is classical/(2l). -/
theorem thetaRootNormalizedMagnitude_eq :
    thetaRootNormalizedMagnitude T =
      qPilotClassicalNormalizedMagnitude T / (2 * l.value : Real) := by
  unfold thetaRootNormalizedMagnitude qPilotClassicalNormalizedMagnitude
  exact qVPilotRootNormalizedMagnitude_eq T

/-- Actual final positive inequality: Theta root normalized magnitude is at
most the q-pilot classical normalized magnitude. -/
theorem thetaRootNormalizedMagnitude_le_qPilotClassical :
    thetaRootNormalizedMagnitude T ≤ qPilotClassicalNormalizedMagnitude T := by
  rw [thetaRootNormalizedMagnitude_eq]
  unfold qPilotClassicalNormalizedMagnitude
  have hq : 0 ≤ nativeQVPilotNormalizedLogMagnitude T :=
    nativeQVPilotNormalizedLogMagnitude_nonneg T
  have hl : (1 : Real) ≤ (2 * l.value : Real) := by
    have hpos : 0 < l.value := l.prime.pos
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) hpos))
  calc
    nativeQVPilotNormalizedLogMagnitude T / (2 * l.value : Real)
        ≤ nativeQVPilotNormalizedLogMagnitude T / 1 :=
          div_le_div_of_nonneg_left hq zero_lt_one hl
    _ = nativeQVPilotNormalizedLogMagnitude T := div_one _

/-- Signed form of the final inequality: -qPilot <= -thetaRoot. -/
theorem neg_qPilotClassical_le_neg_thetaRoot :
    -qPilotClassicalNormalizedMagnitude T ≤
      -thetaRootNormalizedMagnitude T :=
  neg_le_neg_iff.mpr (thetaRootNormalizedMagnitude_le_qPilotClassical T)

/-- Actual final scalar data with the two separate formulas. -/
structure QVPilotThetaFinalScalarData where
  qPilotLocal : Bad (nativePlaceSelection T) → Real
  qPilotLocal_eq : qPilotLocal = qPilotClassicalLocalMagnitude T
  thetaRootLocal : Bad (nativePlaceSelection T) → Real
  thetaRootLocal_eq : thetaRootLocal = thetaRootLocalMagnitude T
  qPilotNormalized : Real
  qPilotNormalized_eq : qPilotNormalized = qPilotClassicalNormalizedMagnitude T
  thetaRootNormalized : Real
  thetaRootNormalized_eq : thetaRootNormalized = thetaRootNormalizedMagnitude T
  finalInequality : thetaRootNormalized ≤ qPilotNormalized

/-- The actual final scalar data constructor. -/
noncomputable def qvPilotThetaFinalScalarData : QVPilotThetaFinalScalarData T where
  qPilotLocal := qPilotClassicalLocalMagnitude T
  qPilotLocal_eq := rfl
  thetaRootLocal := thetaRootLocalMagnitude T
  thetaRootLocal_eq := rfl
  qPilotNormalized := qPilotClassicalNormalizedMagnitude T
  qPilotNormalized_eq := rfl
  thetaRootNormalized := thetaRootNormalizedMagnitude T
  thetaRootNormalized_eq := rfl
  finalInequality := thetaRootNormalizedMagnitude_le_qPilotClassical T

end LeanFormal.IUT.XiFPaper.QVPilotThetaFinalInequalityActual

end
