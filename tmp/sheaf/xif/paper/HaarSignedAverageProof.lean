import tmp.sheaf.xif.paper.HaarThetaAverageProof
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# Deep attempt: hnormal for the signed source-theater PaperSignedHull

Target for the actual C3 with source-theater theta packet:

  (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
    (C6ActualIQData.actual places tuple mu).hull
  = ENNReal.ofReal (c3ThetaSignedProcession C3).average

The actual signed procession is the negative of the unsigned C3 packet
procession:

  (c3ThetaSignedProcession C3).average
    = -((c3ThetaProcession C3).average)
    = -(C3.thetaPacket.logVolume / card).

Actual Haar input is the C6 unit-factor identity

  Real.log (mu (canonicalHull)).toReal
    = arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu (canonicalUnitReference)).toReal,

together with the actual C6 identification of its iqInterface log-volume with
haarLogVolume.  There is no theorem identifying the canonical-hull unit factor
with the signed C3 theta average.  The exact missing analytic identity is:

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu (canonicalUnitReference)).toReal
  = (c3ThetaSignedProcession C3).average,

plus nonnegativity of that signed average (or of the Haar real log) so the
ENNReal.ofReal conversion is faithful.

This file proves the exact signed-average formula and the conditional hnormal
from that missing identity.  No unconditional hnormal is asserted.  No
True/PUnit/axiom/sorry is used.  WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace HaarSignedAverageProof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-! ## 1. Actual signed average formula -/

/-- The signed procession average is minus the unsigned packet average. -/
theorem signedAverage_eq_neg_theta_div_card :
    (c3ThetaSignedProcession C3).average =
      -(C3.thetaPacket.logVolume / (c3ThetaCard (l := l) : Real)) := by
  rw [c3ThetaSignedProcession_average_eq_neg, c3ThetaProcession_average]

/-- Under the exact packet sign field, the signed average is nonnegative. -/
theorem signedAverage_nonneg
    (hlog : ThetaPacketLogVolumeNonpos (C3 := C3)) :
    0 <= (c3ThetaSignedProcession C3).average :=
  c3ThetaSignedProcession_average_nonneg C3 hlog

/-! ## 2. Actual C6 Haar unit-factor identity -/

/-- The actual canonical-hull Haar log is the unit factor plus reference term. -/
theorem haarCanonicalHullLog_eq_unitFactor_signed :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  haarCanonicalHullLog_eq_unitFactor
    (places := places) (tuple := tuple) mu

/-! ## 3. Exact missing signed factorization -/

/-- The exact missing signed identity: the actual canonical-hull unit factor is
the signed C3 theta procession average. -/
def SignedUnitFactorThetaComparison : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    (c3ThetaSignedProcession C3).average

/-- Nonnegativity of the signed average, needed for the ENNReal.ofReal readback. -/
def SignedAverageNonneg : Prop :=
  0 <= (c3ThetaSignedProcession C3).average

/-- The exact missing signed factorization bundle. -/
def ExactMissingSignedHaarThetaFactorization : Prop :=
  SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3 ∧
  SignedAverageNonneg (l := l) (V := V) (I := I) C3

/-- Conditional hnormal from the exact signed factorization: the actual C6 Haar
log-volume equals ENNReal.ofReal of the signed theta average. -/
theorem c6_hnormal_signed_of_missingFactorization
    (h : ExactMissingSignedHaarThetaFactorization
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu C3) :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).hull =
      ENNReal.ofReal (c3ThetaSignedProcession C3).average := by
  rcases h with ⟨hfactor, hnonneg⟩
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  have hfin : haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := by
    rw [haarLogVolume_of_lt_top hmeasure]
    exact ENNReal.ofReal_lt_top
  have hrealLog :
      Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (c3ThetaSignedProcession C3).average := by
    rw [haarCanonicalHullLog_eq_unitFactor
      (places := places) (tuple := tuple) mu]
    exact hfactor
  have hnonnegLog :
      0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal := by
    rw [hrealLog]
    exact hnonneg
  have hreal :
      (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (c3ThetaSignedProcession C3).average := by
    rw [haarLogVolume_of_lt_top hmeasure,
      ENNReal.toReal_ofReal hnonnegLog, hrealLog]
  have hc6 :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) := by
    simp [C6ActualIQData.actual,
      arithmeticTupleIQHullLogVolumeInterface_logVolume,
      arithmeticTupleIQHullLogVolumeInterface_hull]
  rw [hc6, ← ENNReal.ofReal_toReal (ne_of_lt hfin), hreal]

/-! ## 4. Exact missing object -/

/-- The exact missing hnormal identity, as a named proposition. -/
def MissingSignedHaarThetaIdentity : Prop :=
  (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
      (C6ActualIQData.actual places tuple mu).hull =
    ENNReal.ofReal (c3ThetaSignedProcession C3).average

/-- The missing factorization gives the exact missing hnormal identity. -/
theorem missingSignedHaarThetaIdentity_of_factorization
    (h : ExactMissingSignedHaarThetaFactorization
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu C3) :
    MissingSignedHaarThetaIdentity
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu C3 :=
  c6_hnormal_signed_of_missingFactorization
    (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu C3 h

end HaarSignedAverageProof
end XiFPaper
end LeanFormal.IUT
