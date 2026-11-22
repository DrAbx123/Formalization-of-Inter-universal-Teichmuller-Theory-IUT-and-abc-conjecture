import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.n8.closure.C6ActualIQData

/-!
# PaperSignedHull from the actual C6 IQ hull and normalized packet data

This file constructs PaperSignedHull from the actual C6 IQ hull interface and
the actual theta packet/procession normalization data of
SignedHullNormalizationActual.

Actual inputs:
* ambient IQHullLogVolumeInterface = (C6ActualIQData.actual places tuple mu).iqInterface;
* hull packet / reference packet / procession = SignedHullNormalizationActual;
* FiniteHull values = the actual procession log-scales, hull volume = actual
  packetLogVolume;
* ScalingSource supplies the actual theta packet scaling condition (hence
  procession average nonnegativity).

Exact missing hull fields, kept as explicit arguments, not fabricated:
1. hcontains : forall j, procession.value j <= packetLogVolume hullPacket.
   This is the finite-hull containment of the individual log-scales in the
   total packet log-volume; it is a source hull field, not derived here.
2. hnormal : (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
       (C6ActualIQData.actual places tuple mu).hull
     = ENNReal.ofReal procession.average.
   This is the exact paper procession-normalization equality between the actual
   C6 IQ hull Haar log-volume and the theta-packet procession average. It is
   not supplied by C6ActualIQData or by the packet module.

No arbitrary packet, degenerate placeholder, unfilled proof, or forbidden
primitive is introduced. The construction is conditional on the exact fields
above.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.SignedHullNormalizationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota -> Type w}
variable (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable {l : PrimeGeFive}

/-- The actual C6 IQ carrier of the tensor block. -/
abbrev ActualC6Carrier (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> V i) : Type (max u v) :=
  C6IQCarrier places tuple

/-- The actual C6 IQ hull interface. -/
noncomputable def actualC6Interface :
    IQHullLogVolumeInterface (ActualC6Carrier places tuple) :=
  (C6ActualIQData.actual places tuple mu).iqInterface

/-- The finite hull carrier built from the actual procession values and the
actual packet log-volume. The containment field is the explicit source field
hcontains. -/
noncomputable def actualFiniteHull
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l)) :
    FiniteHull (sourceFiniteLabel l) where
  volume j := (SignedHullNormalizationActual.procession l).value j
  hullVolume := packetLogVolume (SignedHullNormalizationActual.hullPacket l)
  contains := hcontains

/-- The actual PaperSignedHull from the C6 IQ hull and normalized packet data,
conditional on the two exact hull fields hcontains and hnormal. -/
noncomputable def paperSignedHullFromSource
    (S : ScalingSource l)
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l))
    (hnormal :
      (actualC6Interface places tuple mu).logVolume
          (actualC6Interface places tuple mu).hull =
        ENNReal.ofReal (SignedHullNormalizationActual.procession l).average) :
    PaperSignedHull (ActualC6Carrier places tuple) (sourceFiniteLabel l) where
  ambient := actualC6Interface places tuple mu
  procession := SignedHullNormalizationActual.procession l
  hull := actualFiniteHull (l := l) hcontains
  weighted_matches_hull := by
    intro j
    rfl
  weights_nonnegative := fun j =>
    SignedHullNormalizationActual.procession_weights_nonnegative (l := l) j
  average_nonneg := procession_average_nonneg S
  hull_logVolume_eq_average := hnormal

/-- The signed hull log-volume of the constructed paper signed hull: the
negative actual C6 hull log-volume, as in PaperSignedHull. -/
noncomputable def paperSignedHullFromSource_signedHullLogVolume
    (S : ScalingSource l)
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l))
    (hnormal :
      (actualC6Interface places tuple mu).logVolume
          (actualC6Interface places tuple mu).hull =
        ENNReal.ofReal (SignedHullNormalizationActual.procession l).average) :
    Real :=
  (paperSignedHullFromSource places tuple mu S hcontains hnormal).signedHullLogVolume

/-- The constructed paper signed hull log-volume is the negative of the actual
C6 IQ hull Haar log-volume. -/
theorem paperSignedHullFromSource_signedHullLogVolume_eq
    (S : ScalingSource l)
    (hcontains : forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l))
    (hnormal :
      (actualC6Interface places tuple mu).logVolume
          (actualC6Interface places tuple mu).hull =
        ENNReal.ofReal (SignedHullNormalizationActual.procession l).average) :
    paperSignedHullFromSource_signedHullLogVolume places tuple mu S hcontains hnormal =
      -((actualC6Interface places tuple mu).logVolume
        (actualC6Interface places tuple mu).hull).toReal :=
  rfl

end LeanFormal.IUT.XiFPaper

end
