import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on haverage and hnormal; the procession sign was corrected later in PaperSignedHullSignedActual. Do not use this file as the target signed hull without checking the sign.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# PaperSignedHull with the actual source-theater theta procession

The procession is the actual source-theater packet procession

  c3ThetaProcession (c3WithSourceTheaterTheta I D),

whose values are Real.log of the concrete source-theater theta scales and whose
weights are the actual uniform finite weights.

Constructed actual hull data:
* FiniteHull values = the actual theatre procession values;
* hullVolume = sum of absolute procession values (an actual finite hull bound);
* containment is proved from the absolute-value sum;
* weighted_matches_hull and weights_nonnegative are rfl/actual.

Two exact source fields are kept explicit and not fabricated:
1. haverage : 0 <= (c3ThetaProcession C3).average.
   The actual source-theater packet has q = 1/5 and its packet log-volume is
   negative in the source direction; PaperSignedHull nevertheless requires a
   nonnegative procession average. This is the exact missing sign field.
2. hnormal : actual C6 iqInterface.logVolume iqInterface.hull
       = ENNReal.ofReal (c3ThetaProcession C3).average.
   This is the exact missing Haar/theta packet average comparison.

Under these two fields the PaperSignedHull is an actual term with the requested
source-theater procession, and PaperProcessionEqC3ThetaProcession is rfl for the
constructed C3. No toy data, forbidden declaration, or unfilled proof is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.ProcessionThetaPacketAverageActual
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

/-- The actual C6 IQ carrier. -/
abbrev PaperC6Carrier : Type (max ua uv) := C6IQCarrier places tuple

/-- The finite hull attached to the actual source-theater procession: values are
the procession values, hullVolume is the sum of their absolute values. -/
noncomputable def sourceTheaterFiniteHull
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    FiniteHull (SignedLabel l.value) where
  volume j := (c3ThetaProcession C3).value j
  hullVolume := Finset.sum Finset.univ
    (fun j : SignedLabel l.value => |(c3ThetaProcession C3).value j|)
  contains j := by
    calc
      (c3ThetaProcession C3).value j <= |(c3ThetaProcession C3).value j| :=
        le_abs_self _
      _ <= Finset.sum Finset.univ
            (fun i : SignedLabel l.value => |(c3ThetaProcession C3).value i|) :=
        Finset.single_le_sum
          (fun i _ => abs_nonneg ((c3ThetaProcession C3).value i))
          (Finset.mem_univ j)

/-- Conditional actual PaperSignedHull with the source-theater procession. -/
noncomputable def paperSignedHullFromTheater
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (haverage : 0 <= (c3ThetaProcession C3).average)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal (c3ThetaProcession C3).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) where
  ambient := (C6ActualIQData.actual places tuple mu).iqInterface
  procession := c3ThetaProcession C3
  hull := sourceTheaterFiniteHull (I := I) C3
  weighted_matches_hull := by
    intro j
    rfl
  weights_nonnegative := c3ThetaProcession_weights_nonnegative C3
  average_nonneg := haverage
  hull_logVolume_eq_average := hnormal

/-- The constructed paper signed hull carries exactly the actual C3 theta
procession. -/
theorem paperSignedHullFromTheater_procession_eq
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (haverage : 0 <= (c3ThetaProcession C3).average)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal (c3ThetaProcession C3).average) :
    (paperSignedHullFromTheater (I := I) places tuple mu C3 haverage hnormal).procession =
      c3ThetaProcession C3 :=
  rfl

/-- Exact source-theater C3: the C3 whose theta packet is the concrete source
theater packet. -/
noncomputable def sourceTheaterC3
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    SourcePilotRegionData (l := l) (V := V) I :=
  c3WithSourceTheaterTheta I D

/-- The source-theater PaperSignedHull, conditional on the two exact fields. -/
noncomputable def sourceTheaterPaperSignedHull
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (haverage : 0 <= (c3ThetaProcession (sourceTheaterC3 (l := l) (V := V) I D)).average)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaProcession (sourceTheaterC3 (l := l) (V := V) I D)).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  paperSignedHullFromTheater (I := I) places tuple mu
    (sourceTheaterC3 (l := l) (V := V) I D) haverage hnormal

/-- ProcessionEqC3ThetaProcession holds by construction for the source-theater
C3 and the source-theater PaperSignedHull. -/
theorem sourceTheaterPaperSignedHull_paperProcessionEq
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (haverage : 0 <= (c3ThetaProcession (sourceTheaterC3 (l := l) (V := V) I D)).average)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaProcession (sourceTheaterC3 (l := l) (V := V) I D)).average) :
    ProcessionThetaPacketAverageActual.PaperProcessionEqC3ThetaProcession
      (l := l) (sourceTheaterC3 (l := l) (V := V) I D)
      (sourceTheaterPaperSignedHull (l := l) (V := V) (I := I)
        places tuple mu D haverage hnormal) :=
  rfl

end LeanFormal.IUT.XiFPaper

end
