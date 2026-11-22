import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual
import tmp.sheaf.xif.paper.SignedHullFromSource
import tmp.sheaf.xif.paper.HaarThetaAverageProof
import tmp.sheaf.xif.paper.XiFInequalityProof1

/-!
# Actual C3 / PaperSignedHull construction and xi-f magnitude comparison

This file combines actual objects:

* actual C3 from the exact C3 donor record D, with the concrete source-theater
  theta packet (ThetaPacketQIdentificationActual.c3WithSourceTheaterTheta).
  Its theta packet q is the actual 1/5, so the packet contracts unconditionally.
* actual PaperSignedHull from the actual C6 IQ carrier and the actual
  SignedHullNormalizationActual packet/procession (SignedHullFromSource).
  Its construction is conditional on the two exact source hull fields
  hcontains and hnormal.
* the canonical C3 theta-packet procession c3ThetaProcession.

Proved:
* the actual source-theater C3 packet contracts (q = 1/5 <= 1);
* its canonical packet procession has nonpositive average;
* the actual q-pilot magnitude is positive;
* if the actual paper procession is identified with the canonical C3 packet
  procession, then PaperThetaMagnitudeComparison actualC3 actualP follows.
  No ThetaPacketQIdentification is needed for this actual C3, because its
  source-theater q contraction is unconditional.

Exact remaining gaps:
1. hcontains : finite-hull containment for the actual PaperSignedHull;
2. hnormal : actual C6 Haar log-volume = ENNReal.ofReal procession.average
   (the Haar/theta factorization missing object);
3. PaperProcessionEqC3ThetaProcession actualC3 actualP:
   actualP.procession = c3ThetaProcession actualC3.

No toy/True/PUnit/axiom/sorry is used; no missing field is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace PaperThetaMagnitudeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.SignedHullNormalizationActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeComparisonProof
open LeanFormal.IUT.XiFPaper.XiFInequalityProof1
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {W : iota -> Type w}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- The actual C3 object with the concrete source-theater theta packet. -/
noncomputable def actualC3
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    SourcePilotRegionData (l := l) (V := V) I :=
  c3WithSourceTheaterTheta (I := I) D

/-- The actual source-theater C3 packet contracts: q = 1/5 <= 1. -/
theorem actualC3_thetaPacket_contraction
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (actualC3 (l := l) (V := V) (I := I) D).thetaPacket.q <= 1 :=
  c3WithSourceTheaterTheta_q_le_one (I := I) D

/-- The actual canonical C3 packet procession has nonpositive average. -/
theorem actualC3_procession_average_nonpos
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (c3ThetaProcession (actualC3 (l := l) (V := V) (I := I) D)).average <= 0 := by
  rw [c3ThetaProcession_average]
  exact actualThetaPacketAverage_nonpos
    (actualC3 (l := l) (V := V) (I := I) D)
    (actualC3_thetaPacket_contraction (l := l) (V := V) (I := I) D)

/-- The actual paper signed hull from the actual C6 IQ carrier and actual
normalized packet procession, conditional on the two exact hull fields. -/
noncomputable def actualPaperSignedHull
    (S : ScalingSource l)
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal (SignedHullNormalizationActual.procession l).average) :
    PaperSignedHull (ActualC6Carrier places tuple) (sourceFiniteLabel l) :=
  paperSignedHullFromSource places tuple mu S hcontains hnormal

/-- The actual q-pilot magnitude of the source-theater C3 is positive. -/
theorem actualC3_qPilotLogMagnitude_pos
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    0 < paperQPilotLogMagnitude
      (actualC3 (l := l) (V := V) (I := I) D) :=
  LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeComparisonProof.paperQPilotLogMagnitude_pos
    (actualC3 (l := l) (V := V) (I := I) D)

/-- Actual comparison theorem: for the actual source-theater C3 and the actual
paper signed hull, the procession identification is the only remaining
comparison-side gap. The q-packet contraction is actual (q = 1/5), so no
ThetaPacketQIdentification is required. -/
theorem paperThetaMagnitudeComparison_actual
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (S : ScalingSource l)
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal (SignedHullNormalizationActual.procession l).average)
    (hProc : PaperProcessionEqC3ThetaProcession (l := l)
      (actualC3 (l := l) (V := V) (I := I) D)
      (actualPaperSignedHull (l := l) places tuple mu S hcontains hnormal)) :
    PaperThetaMagnitudeComparison
      (actualC3 (l := l) (V := V) (I := I) D)
      (actualPaperSignedHull (l := l) places tuple mu S hcontains hnormal) := by
  unfold PaperThetaMagnitudeComparison
  change (actualPaperSignedHull (l := l) places tuple mu S hcontains
      hnormal).procession.average <=
    paperQPilotLogMagnitude (actualC3 (l := l) (V := V) (I := I) D)
  have hproc : (actualPaperSignedHull (l := l) places tuple mu S hcontains
      hnormal).procession =
      c3ThetaProcession (actualC3 (l := l) (V := V) (I := I) D) := hProc
  rw [hproc]
  exact le_trans
    (actualC3_procession_average_nonpos (l := l) (V := V) (I := I) D)
    (le_of_lt (actualC3_qPilotLogMagnitude_pos (l := l) (V := V) (I := I) D))

/-- Exact remaining comparison-side object: the actual paper procession must be
identified with the canonical C3 theta-packet procession. -/
def MissingActualProcessionIdentification
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  forall (S : ScalingSource l)
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal (SignedHullNormalizationActual.procession l).average),
    PaperProcessionEqC3ThetaProcession (l := l)
      (actualC3 (l := l) (V := V) (I := I) D)
      (actualPaperSignedHull (l := l) places tuple mu S hcontains hnormal)

end PaperThetaMagnitudeActual
end XiFPaper
end LeanFormal.IUT
end
