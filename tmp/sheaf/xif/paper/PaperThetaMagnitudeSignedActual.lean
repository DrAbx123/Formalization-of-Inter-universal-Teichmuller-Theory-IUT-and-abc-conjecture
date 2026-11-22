import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeComparisonProof
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on SignedHnormal and SignedThetaAverageLeQMagnitude. Does NOT construct unconditional paper xi-f. The signed average/procession objects are actual, but the C6 Haar normalization and the direct signed magnitude comparison are still missing; no inequality is asserted.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual PaperThetaMagnitudeComparison with the signed source-theater hull

This file constructs the actual signed source-theater objects:

* actualSignedC3 D := sourceTheaterC3Signed I D, whose theta packet is the
  concrete source-theater packet q = 1/5;
* actualSignedHull D hnormal := sourceTheaterSignedPaperSignedHull I D hlog hnormal,
  where hlog is PROVED from q = 1/5 and hnormal is the exact C6 Haar comparison;
* actualSignedHull has procession c3ThetaSignedProcession actualSignedC3 by rfl.

The target PaperThetaMagnitudeComparison for these actual objects is exactly
the signed-average/q-magnitude comparison:

  (c3ThetaSignedProcession actualSignedC3).average
    <= paperQPilotLogMagnitude actualSignedC3.

That is the exact missing source comparison. The C6 Haar field hnormal is the
only remaining object-construction field. No toy/True/PUnit/axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace PaperThetaMagnitudeSignedActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.XiFInequalityProof1
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeComparisonProof
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uL uC uG uX uLabel

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

/-- The actual source-theater signed C3. -/
abbrev actualSignedC3
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    SourcePilotRegionData (l := l) (V := V) I :=
  sourceTheaterC3Signed (l := l) (V := V) D

/-- The actual source-theater C3 theta packet contracts, so its log-volume is
nonpositive (hlog is proved, not assumed). -/
theorem actualSignedC3_hlog
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    ThetaPacketLogVolumeNonpos (actualSignedC3 (l := l) (V := V) D) := by
  unfold ThetaPacketLogVolumeNonpos actualSignedC3 sourceTheaterC3Signed
  apply thetaPacket_logVolume_nonpos
  exact c3WithSourceTheaterTheta_q_le_one (I := I) D

/-- The exact C6 Haar comparison field for the signed procession. -/
abbrev SignedHnormal
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
      (C6ActualIQData.actual places tuple mu).iqInterface.hull =
    ENNReal.ofReal
      (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) D)).average

/-- The actual signed source-theater PaperSignedHull, conditional only on the
C6 Haar comparison field. -/
noncomputable def actualSignedHull
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hnormal : SignedHnormal (l := l) (V := V) (I := I)
      places tuple mu D) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  sourceTheaterSignedPaperSignedHull (l := l) (V := V) (I := I)
    places tuple mu D (actualSignedC3_hlog (l := l) (V := V) (I := I) D)
    hnormal

/-- The actual signed hull carries the signed packet procession. -/
theorem actualSignedHull_procession_eq
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hnormal : SignedHnormal (l := l) (V := V) (I := I)
      places tuple mu D) :
    (actualSignedHull (l := l) (V := V) (I := I)
        places tuple mu D hnormal).procession =
      c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) D) :=
  rfl

/-- Exact missing source comparison: the signed theta procession average is at
most the actual q-pilot magnitude. -/
def SignedThetaAverageLeQMagnitude
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) D)).average <=
    paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) D)

/-- The target PaperThetaMagnitudeComparison for the actual signed objects is
exactly the signed-average/q-magnitude comparison. -/
theorem paperThetaMagnitudeComparison_actualSigned_iff
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hnormal : SignedHnormal (l := l) (V := V) (I := I)
      places tuple mu D) :
    PaperThetaMagnitudeComparison
        (actualSignedC3 (l := l) (V := V) D)
        (actualSignedHull (l := l) (V := V) (I := I)
          places tuple mu D hnormal) ↔
      SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D := by
  unfold PaperThetaMagnitudeComparison SignedThetaAverageLeQMagnitude
  change (actualSignedHull (l := l) (V := V) (I := I)
      places tuple mu D hnormal).procession.average <=
    paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) D) ↔
    (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) D)).average <=
    paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) D)
  rw [actualSignedHull_procession_eq]

/-- Conditional actual construction of the target from the exact signed-average
comparison. -/
theorem paperThetaMagnitudeComparison_actualSigned
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hnormal : SignedHnormal (l := l) (V := V) (I := I)
      places tuple mu D)
    (hbound : SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D) :
    PaperThetaMagnitudeComparison
      (actualSignedC3 (l := l) (V := V) D)
      (actualSignedHull (l := l) (V := V) (I := I)
        places tuple mu D hnormal) :=
  (paperThetaMagnitudeComparison_actualSigned_iff
    (l := l) (V := V) (I := I) places tuple mu D hnormal).mpr hbound

/-- Exact missing object: C6 Haar comparison plus the signed-average bound.
Both are explicit source comparisons; no field is asserted. -/
structure MissingSignedActualComparison
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop where
  hnormal : SignedHnormal (l := l) (V := V) (I := I) places tuple mu D
  signed_average_le_q : SignedThetaAverageLeQMagnitude
    (l := l) (V := V) (I := I) D

/-- From the exact missing signed comparison object, the target actual
PaperThetaMagnitudeComparison follows. -/
theorem paperThetaMagnitudeComparison_actualSigned_of_missing
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (M : MissingSignedActualComparison (l := l) (V := V) (I := I)
      places tuple mu D) :
    PaperThetaMagnitudeComparison
      (actualSignedC3 (l := l) (V := V) D)
      (actualSignedHull (l := l) (V := V) (I := I)
        places tuple mu D M.hnormal) :=
  paperThetaMagnitudeComparison_actualSigned
    (l := l) (V := V) (I := I) places tuple mu D M.hnormal
    M.signed_average_le_q

end PaperThetaMagnitudeSignedActual
end XiFPaper
end LeanFormal.IUT
end
