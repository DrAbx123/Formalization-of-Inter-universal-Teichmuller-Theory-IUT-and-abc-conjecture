import tmp.sheaf.xif.paper.S3133QPilotReadoutActual
import tmp.sheaf.xif.paper.S3133QPilotBatchAInputActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-!
# Sign and positivity of the actual q-pilot log-volume

Source: IUT III, §3, p. 16 (iut3.txt lines 891-893): the log-volume of the
q-pilot object is denoted -|log q| in R, so |log q| > 0.  IUT III, Corollary
3.12, pp. 173-174: -|log(Theta)| >= -|log q| with -|log q| a negative real.
IUT III, Remark 3.1.1, (ii)-(iv): the procession-normalized log-volume uses the
positive weights 1/N_v.

From the actual q_v family and the actual place weights, this file proves the
paper's sign statements:

* the actual total q_v log-magnitude sum_b |log q_v(b)| is positive whenever
  V_bad is nonempty (the native bad index is finite by Fintype);
* the actual q-pilot log-volume qPilotQGlobalLogVolume = -|log q| is strictly
  negative in that case, and its magnitude is the total q_v log-magnitude;
* the actual procession-normalized q-pilot log-volume is strictly negative, and
  its magnitude nativeQVPilotNormalizedLogMagnitude is positive, using the
  actual positive Remark 3.1.1 weights.

No inequality between q-pilot and Theta-pilot is asserted.  No toy/True/PUnit/
axiom/sorry.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual
open LeanFormal.IUT.XiFPaper.S3133QPilotBatchAInputActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual completion degree [K_w : (F_mod)_v] is at least one. -/
theorem one_le_localCompletionDegree' (w : NumberField.FinitePlace X.S.arithmetic.K) :
    1 <= localCompletionDegree X.S.arithmetic w := by
  unfold localCompletionDegree
  exact one_le_finrank_adicCompletion (k := X.S.arithmetic.Fmod) w

/-- The actual Remark 3.1.1 place weights are positive. -/
theorem nativeBadLocalWeight_pos' (b : Bad (nativePlaceSelection X.S)) :
    0 < nativeBadLocalWeight X.S b := by
  unfold nativeBadLocalWeight localNormalizedWeight
  exact inv_pos.mpr (by
    have hdeg := one_le_localCompletionDegree' X (nativeBadToKPlace X.S b)
    have hpos : 0 < localCompletionDegree X.S.arithmetic (nativeBadToKPlace X.S b) :=
      lt_of_lt_of_le Nat.zero_lt_one hdeg
    exact_mod_cast hpos)

/-- The actual total q_v log-magnitude is positive when V_bad is nonempty. -/
theorem totalLocalLogMagnitude_pos
    [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))] :
    0 < ∑ b : Bad (nativePlaceSelection X.S),
      localLogMagnitude (qVFamily X.S b) := by
  apply Finset.sum_pos
  · intro b _
    exact localLogMagnitude_pos (qVFamily X.S b)
  · exact Finset.univ_nonempty

/-- The actual total q_v log-magnitude is nonnegative. -/
theorem totalLocalLogMagnitude_nonneg
    [Fintype (Bad (nativePlaceSelection X.S))] :
    0 <= ∑ b : Bad (nativePlaceSelection X.S),
      localLogMagnitude (qVFamily X.S b) := by
  apply Finset.sum_nonneg
  intro b _
  exact le_of_lt (localLogMagnitude_pos (qVFamily X.S b))

/-- The actual q-pilot log-volume is nonpositive: it is a signed log-volume. -/
theorem qPilotQGlobalLogVolume_nonpos
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotQGlobalLogVolume X <= 0 := by
  rw [qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude]
  exact neg_nonpos.mpr (totalLocalLogMagnitude_nonneg X)

/-- The actual q-pilot log-volume -|log q| is strictly negative when V_bad is
nonempty: this is the paper's |log q| > 0. -/
theorem qPilotQGlobalLogVolume_neg
    [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))] :
    qPilotQGlobalLogVolume X < 0 := by
  rw [qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude]
  exact neg_neg_of_pos (totalLocalLogMagnitude_pos X)

/-- The magnitude |log q| of the actual q-pilot log-volume is positive when
V_bad is nonempty. -/
theorem qPilotQGlobalLogMagnitude_pos
    [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))] :
    0 < -qPilotQGlobalLogVolume X :=
  neg_pos.mpr (qPilotQGlobalLogVolume_neg X)

/-- The magnitude of the actual q-pilot log-volume is the total q_v
log-magnitude. -/
theorem qPilotQGlobalLogMagnitude_eq_total
    [Fintype (Bad (nativePlaceSelection X.S))] :
    -qPilotQGlobalLogVolume X =
      ∑ b : Bad (nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b) := by
  rw [qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude, neg_neg]

/-- The actual procession-normalized q-pilot log-magnitude is positive when
V_bad is nonempty, by positivity of the actual place weights. -/
theorem nativeNormalizedLogMagnitude_pos
    [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))] :
    0 < nativeQVPilotNormalizedLogMagnitude X.S := by
  unfold nativeQVPilotNormalizedLogMagnitude
  apply Finset.sum_pos
  · intro b _
    exact mul_pos (nativeBadLocalWeight_pos' X b)
      (nativeQVPilotLocalMagnitude_pos X.S b)
  · exact Finset.univ_nonempty

/-- The actual procession-normalized q-pilot log-volume is strictly negative when
V_bad is nonempty. -/
theorem qPilotNormalizedGlobalReadout_neg
    [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    qPilotNormalizedGlobalReadout X h < 0 := by
  rw [qPilotNormalizedGlobalReadout_eq X h]
  exact neg_neg_of_pos (nativeNormalizedLogMagnitude_pos X)

end LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual
