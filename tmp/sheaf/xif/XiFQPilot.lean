import tmp.sheaf.xif.SourceXiFConstruction
import tmp.sheaf.n8.closure.C9Paper
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion

/-! # Normalized q-pilot log-volume for xi-f

The actual source q-pilot log-volume of SourceXiFConstruction is

  sourceQPilotLogVolume = sourceLocalLogDegree(sourceQPilotPoint).

Its normalized value divides by the cardinality of SourceVolumeIndex l.
sourceQPilotLogVolume_eq_gauss gives the raw value as
card * Real.log thetaPacket.q, so the normalized value is
Real.log thetaPacket.q.

The paper C9Paper.QPaper.qPilotLogVolume is localSignedLog C3.q.  Connecting
it to the source normalized value requires two source-level identifications:

* C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q (packet q identification);
* localSignedLog C3.q = -Real.log C3.thetaPacket.q (q scalar identification).

Both are kept as explicit hypotheses in the paper-connection theorem.  No
unconditional identification is asserted; that is the exact source gap.

## Value-layer/surrogate status (audit task-491)

This file is a VALUE-LAYER CONDITIONAL SURROGATE, not paper-level xi-f.

Exact mismatches:

1. sourceQPilotPoint is the theta-pilot point at signed label 1, not the
   actual (1,0) q-pilot object of the paper.
2. sourceQPilotLogVolume is card * Real.log thetaPacket.q (861 * log q at
   l=41), and its normalized value is Real.log thetaPacket.q.  It is not the
   paper q-pilot log-volume -|log q|.
3. sourceThetaHullLogVolume is the supremum of pointwise source log-degrees
   over the source holomorphic hull, not the paper 1,circ U holomorphic-hull
   log-volume.
4. The hScaling condition in sourceXiFInclusion is substantive; it is not
   discharged here.

Consequently no target_accepted or paper-level xi-f claim is made.  The
paper-level q-pilot object, signed 1,circ U hull, O-module/vector-bundle layer,
and paper inclusion are separate tasks and must not be substituted by this
surrogate.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
universe uL

/-- Normalized q-pilot log-volume: the actual source q-pilot log-volume divided
by the cardinality of the source volume index. -/
def sourceNormalizedQPilotLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Real :=
  I.sourceQPilotLogVolume v R n / (Fintype.card (SourceVolumeIndex l) : Real)

/-- The normalized q-pilot log-volume is the logarithm of the source theta-packet q. -/
theorem sourceNormalizedQPilotLogVolume_eq_log_q (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceNormalizedQPilotLogVolume v R n =
      Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
  unfold sourceNormalizedQPilotLogVolume
  rw [I.sourceQPilotLogVolume_eq_gauss v R n]
  have hcard : (Fintype.card (SourceVolumeIndex l) : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sourceVolumeIndex_card_pos l))
  exact mul_div_cancel_left₀ (Real.log ((I.theaterAt 0 0).thetaPacket.q)) hcard

/-- The negative signed normalized q-pilot log-volume. -/
def sourceNormalizedQPilotSignedLogVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  - I.sourceNormalizedQPilotLogVolume v R n

/-- The signed normalized value is the negative logarithm. -/
theorem sourceNormalizedQPilotSignedLogVolume_eq_neg_log_q (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceNormalizedQPilotSignedLogVolume v R n =
      - Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
  unfold sourceNormalizedQPilotSignedLogVolume
  rw [I.sourceNormalizedQPilotLogVolume_eq_log_q v R n]

/-- Conditional connection to the paper q-pilot log-volume.

The paper value is C9Paper.QPaper.qPilotLogVolume = localSignedLog C3.q, a
WithTop Real.  The source normalized value is Real.log thetaPacket.q.  The
following source-level identifications are explicit hypotheses, not derived:

* hPacket: C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q;
* hScalar: localSignedLog C3.q = -Real.log C3.thetaPacket.q.

Under them, the paper q-pilot log-volume is the negative signed normalized
source value.  This is a value-layer/surrogate comparison, not the paper-level
xi-f q-pilot object. -/
theorem sourceNormalizedQPilotLogVolume_eq_paper_neg
    {Label : Type uL} [Group Label]
    {D : ABCBridge.N8.C4Actual.SourceWitnessedOutputData (l := l) (V := V) I Label}
    {C1 : N8Closure.SourceInputBinding.SourceInputBinding I}
    {C2 : N8Closure.SourceLogKummerRealization.SourceLogKummerData I C1}
    (C3 : N8Closure.SourcePilotRegion.SourcePilotRegionData (l := l) (V := V) I)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (Q : N8Closure.C9Paper.QPaper (D := D) (C1 := C1) (C2 := C2) (C3 := C3))
    (hPacket : C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q)
    (hScalar : ArithmeticQPilotLogVolume.localSignedLog C3.q =
      - Real.log C3.thetaPacket.q) :
    Q.qPilotLogVolume =
      (- I.sourceNormalizedQPilotLogVolume v R n : WithTop Real) := by
  have hQ : Q.qPilotLogVolume =
      (ArithmeticQPilotLogVolume.localSignedLog C3.q : WithTop Real) := by
    rw [Q.qPilotLogVolume_eq, Q.scalar.value_eq]
  rw [hQ, hScalar, hPacket, I.sourceNormalizedQPilotLogVolume_eq_log_q v R n]
  simp

end OriginalInput
end Theorem311Source

end IUT
