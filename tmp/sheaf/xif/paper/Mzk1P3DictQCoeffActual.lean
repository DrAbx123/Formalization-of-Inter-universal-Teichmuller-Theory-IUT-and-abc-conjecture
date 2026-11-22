import tmp.sheaf.xif.paper.Mzk1P3DictBArithActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import tmp.sheaf.xif.paper.Mzk1WeightedDetPacketInstanceActual
import Mathlib.Tactic

/-!
# Mzk1P3DictQCoeffActual

Exact paper Q-coefficient algebra and the native q sign source.

Pure algebra (green):
  ((l+1)/24) * logq = sL l * AL l logq,
where sL l = l(l+1)/12 and AL l logq = logq/(2l).

Native candidate:
  nativeSignedLogQ T := -nativeQArith T
  nativePaperA T := nativeQArith T/(2l)
  ((l+1)/24) * nativeSignedLogQ T = - sL l * nativePaperA T
because nativeQArith is the positive weighted |log q| sum.

The identification nativeSignedLogQ = paper log q is the explicit source object
PaperLogQSource, not asserted.  DICT-B remains INTERFACE.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictBArithActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketInstanceActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

/-- Pure algebra: the paper Q coefficient equals sF * A. -/
theorem paperQCoeff_eq_sL_AL (l logq : Real) (hl : l ≠ 0) :
    ((l + 1) / 24) * logq = sL l * AL l logq := by
  unfold sL AL
  have h2 : (2 * l : Real) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hl
  field_simp [hl, h2]
  ring

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Native signed log q candidate: negative of the positive weighted magnitude. -/
noncomputable def nativeSignedLogQ : Real :=
  -nativeQArith T

/-- Native A candidate: |log q|/(2l). -/
noncomputable def nativePaperA : Real :=
  nativeQArith T / (2 * (l.value : Real))

/-- Exact native coefficient relation. -/
theorem nativePaperQ_eq_neg_sL_mul_A :
    ((l.value + 1) / 24) * nativeSignedLogQ T =
      - sL (l.value : Real) * nativePaperA T := by
  unfold nativeSignedLogQ nativePaperA
  rw [paperQCoeff_eq_sL_AL (l := (l.value : Real)) (logq := -nativeQArith T)
    (by exact_mod_cast l.prime.ne_zero)]
  unfold AL
  ring

/-- Explicit source object: the paper signed log q is the negative native
weighted magnitude. -/
structure PaperLogQSource where
  logQ : Real
  logQ_eq : logQ = nativeSignedLogQ T

/-- The paper Q coefficient computed from a PaperLogQSource. -/
noncomputable def paperQCoeffFromSource (S : PaperLogQSource (l := l) T) : Real :=
  ((l.value + 1) / 24) * S.logQ

/-- The source logQ gives the paper Q coefficient; its A-form still needs the
sign/normalization dictionary recorded in P3-TARGET-EQUIV. -/
theorem paperQCoeffFromSource_eq (S : PaperLogQSource (l := l) T) :
    paperQCoeffFromSource (l := l) T S =
      ((l.value + 1) / 24) * nativeSignedLogQ T := by
  unfold paperQCoeffFromSource
  rw [S.logQ_eq]


/-- nativeQArith is the weighted base-q magnitude sum. -/
theorem nativeQArith_eq_weighted_sum :
    nativeQArith T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold nativeQArith
  exact nativeGlobalQPilotNormalizedLogMagnitude_eq T

/-- Exact remaining q-half source: weighted native sum equals the unweighted
base-q total log-magnitude.  This is the weight-one gap (GAP-PC-WEIGHT). -/
def GAP_PC_QHALF : Prop :=
  nativeQArith T = baseQTotalLogMagnitude T

/-- Conditional actual q-packet source. -/
theorem qPacket_normalized_eq_neg_nativeQArith_div_of_qhalf
    (hQ : GAP_PC_QHALF (l := l) T) :
    (qPacket (l := l) T).normalizedLogVolume =
      -nativeQArith T / (2 * (l.value : Real)) := by
  rw [qPacket_normalized_eq_qActualBase]
  unfold qActualBaseNormalized
  rw [← hQ]

/-- Conditional signed log q / 2l identification.  The actual q packet gives
the unweighted sum; equality with nativeQArith needs GAP_PC_QHALF. -/
theorem nativeSignedLogQ_eq_twoL_mul_qPacket_of_qhalf
    (hQ : GAP_PC_QHALF (l := l) T) :
    nativeSignedLogQ T =
      (2 * (l.value : Real)) *
        (qPacket (l := l) T).normalizedLogVolume := by
  unfold nativeSignedLogQ
  rw [qPacket_normalized_eq_neg_nativeQArith_div_of_qhalf (l := l) T hQ]
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  field_simp [hl]


/-- QHALF is implied by GAP-PC-WEIGHT (all nativeBadLocalWeight = 1):
the weighted native sum collapses to the unweighted base-q total. -/
theorem GAP_PC_QHALF_of_weight_one
    (hweight : forall b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = 1) :
    GAP_PC_QHALF (l := l) T := by
  unfold GAP_PC_QHALF
  rw [nativeQArith_eq_weighted_sum, baseQTotalLogMagnitude_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [hweight b]
  ring

/-- Conditional q-packet source under the weight-one hypothesis. -/
theorem nativeSignedLogQ_eq_twoL_mul_qPacket_of_weight_one
    (hweight : forall b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = 1) :
    nativeSignedLogQ T =
      (2 * (l.value : Real)) *
        (qPacket (l := l) T).normalizedLogVolume :=
  nativeSignedLogQ_eq_twoL_mul_qPacket_of_qhalf (l := l) T
    (GAP_PC_QHALF_of_weight_one (l := l) T hweight)

#check nativeQArith_eq_weighted_sum
#check GAP_PC_QHALF
#check qPacket_normalized_eq_neg_nativeQArith_div_of_qhalf
#check GAP_PC_QHALF_of_weight_one
#check nativeSignedLogQ_eq_twoL_mul_qPacket_of_weight_one
#check nativeSignedLogQ_eq_twoL_mul_qPacket_of_qhalf

#check paperQCoeff_eq_sL_AL
#check nativeSignedLogQ
#check nativePaperA
#check nativePaperQ_eq_neg_sL_mul_A
#check PaperLogQSource
#check paperQCoeffFromSource_eq

end LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual

end
