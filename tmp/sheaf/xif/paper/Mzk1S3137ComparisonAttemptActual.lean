/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import Mathlib.Tactic

/-! A520: attempt at the faithful S3137 comparison Q_C <= H_C.

Setup (all green):
  Q_C(P) = qPilotLogVolumeReading P = -|log ||q||| <= 0;
  H_C    = thetaPilotHullLogVolumeReal C3 = log (Haar (thetaPilotHull C3)).
Target: qThetaPilotLogVolumeComparison C3 P (Q_C <= H_C).

Result: the comparison is NOT derivable from the current data:
  * H_C is the raw log of Measure.addHaar, an arbitrary additive Haar measure:
    it is fixed only up to an additive constant, and no paper normalization
    (Prop 3.9(i) base choice) is fixed in S3137;
  * Q_C is genuinely data-dependent (-|log q|), so no sign argument proves the
    comparison (if H_C < 0 the comparison is a real inequality |H_C| <= |log q|).

What is proved here:
  1. H_C = [block : Q_p] * c3PacketNormalizedLogVolume(C3, Haar, hull),
     i.e. the raw hull readout is the Q_p-dimension times the packet-normalized
     log-volume (uses c3TensorBlockDimension_pos);
  2. the comparison reduces to the explicit real arithmetic inequality
     -|log q| <= H_C (S3137ComparisonArithmetic);
  3. sufficient condition: if the hull log-volume readout is nonnegative
     (equivalently the Haar of the actual region is >= 1), the comparison holds,
     because Q_C <= 0; this is the only provable part from the current data;
  4. the p-scaling of the normalized hull readout (Prop 3.9(i)), so any future
     normalization choice can be transported.

The missing input is thus a NORMALIZATION/containment theorem: the paper's
procession-normalized Theta-hull log-volume (with the Haar base fixed by
Prop 3.9(i) and the possible-images containment of xi-e) must be identified
with H_C; the comparison itself is Cor 3.12, not a definitional identity. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonAttemptActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance s3137cmpBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance s3137cmpBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. Raw hull readout = dimension * packet-normalized readout -/

theorem thetaPilotHullLogVolumeReal_eq_dim_mul_normalized :
    thetaPilotHullLogVolumeReal C3 =
      (c3TensorBlockDimension C3 : Real) *
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
          (thetaPilotHull C3) := by
  rw [thetaPilotHullLogVolumeReal_eq_regionLogVolume]
  unfold c3PacketNormalizedLogVolume
  have hdim : (c3TensorBlockDimension C3 : Real) != 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  field_simp
  ring

/-! ## 2. Explicit arithmetic reduction of the comparison -/

/-- The explicit real-arithmetic inequality behind the S3137 comparison:
`-A <= H` for the q-magnitude A = |log ||q||| and hull readout H. -/
def S3137ComparisonArithmetic (A H : Real) : Prop :=
  -A <= H

theorem qThetaPilotLogVolumeComparison_iff_arithmetic
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qThetaPilotLogVolumeComparison C3 P <->
      S3137ComparisonArithmetic
        (|Real.log (‖P.line.C3.q.q‖)|) (thetaPilotHullLogVolumeReal C3) := by
  rw [qThetaPilotLogVolumeComparison_iff,
    qPilotLogVolumeReading_eq_neg_abs_qParameter]
  exact Iff.rfl

theorem arithmetic_iff_nonneg_sum {A H : Real} (hA : 0 <= A) :
    S3137ComparisonArithmetic A H <-> 0 <= H + A := by
  unfold S3137ComparisonArithmetic
  constructor <;> intro h <;> linarith

/-! ## 3. The provable sufficient condition -/

theorem thetaPilotHullLogVolumeReal_sign_of_haar {C3 : SourcePilotRegionData (l := l)
    (V := V) I}
    (h : 1 <= (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    0 <= thetaPilotHullLogVolumeReal C3 := by
  rw [thetaPilotHullLogVolumeReal_eq_regionLogVolume]
  exact Real.log_nonneg h

/-- If the actual hull Haar is normalized so that the hull has measure >= 1,
the faithful comparison holds: the q-side is nonpositive. -/
theorem qThetaPilotLogVolumeComparison_of_hullLogVolume_nonneg
    (P : PaperQPilotObjectActual (l := l) (I := I))
    (hH : 0 <= thetaPilotHullLogVolumeReal C3) :
    qThetaPilotLogVolumeComparison C3 P := by
  rw [qThetaPilotLogVolumeComparison_iff,
    qPilotLogVolumeReading_eq_neg_abs_qParameter]
  have hq : -|Real.log (‖P.line.C3.q.q‖)| <= 0 :=
    neg_nonpos.mpr (abs_nonneg _)
  linarith

theorem qThetaPilotLogVolumeComparison_of_normalized_nonneg
    (P : PaperQPilotObjectActual (l := l) (I := I))
    (hN : 0 <= c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
      (thetaPilotHull C3)) :
    qThetaPilotLogVolumeComparison C3 P := by
  apply qThetaPilotLogVolumeComparison_of_hullLogVolume_nonneg C3 P
  rw [thetaPilotHullLogVolumeReal_eq_dim_mul_normalized]
  exact mul_nonneg (Nat.cast_nonneg _) hN

/-! ## 4. p-scaling of the normalized hull readout (Prop 3.9(i)) -/

theorem c3Hull_normalizedLogVolume_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3) =
      -Real.log (C3.p : Real) +
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
          (thetaPilotHull C3) := by
  rw [thetaPilotHull_eq_region]
  exact c3PacketNormalizedLogVolume_prime_smul (C3 := C3)
    (actualC3LogShellTensorHaar C3) hpos
    (thetaPilotHull_measure_lt_top (C3 := C3))

/-! ## 5. The comparison attempt object -/

/-- The S3137 comparison attempt data: readings, the exact arithmetic form,
and the normalization hypothesis under which the comparison is proved. -/
structure S3137ComparisonAttempt
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) where
  qReading : Real
  qReading_eq : qReading = qPilotLogVolumeReading P
  thetaHullReading : Real
  thetaHullReading_eq : thetaHullReading = thetaPilotHullLogVolumeReal C3
  arithmeticForm : S3137ComparisonArithmetic
    (|Real.log (‖P.line.C3.q.q‖)|) thetaHullReading
  arithmeticForm_eq : arithmeticForm =
    S3137ComparisonArithmetic (|Real.log (‖P.line.C3.q.q‖)|) thetaHullReading

noncomputable def s3137ComparisonAttempt
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    S3137ComparisonAttempt C3 P where
  qReading := qPilotLogVolumeReading P
  qReading_eq := rfl
  thetaHullReading := thetaPilotHullLogVolumeReal C3
  thetaHullReading_eq := rfl
  arithmeticForm := S3137ComparisonArithmetic
    (|Real.log (‖P.line.C3.q.q‖)|) (thetaPilotHullLogVolumeReal C3)
  arithmeticForm_eq := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonAttemptActual