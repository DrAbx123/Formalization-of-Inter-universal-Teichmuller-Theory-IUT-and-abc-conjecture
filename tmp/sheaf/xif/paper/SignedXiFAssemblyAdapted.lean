import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeActual
import tmp.sheaf.xif.paper.XiFInequalityProof1
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual

/-!
# Signed source-theater xi-f assembly

Combines the actual signed source-theater `PaperSignedHull` from
PaperSignedHullSignedActual with the actual source-theater C3 from
PaperThetaMagnitudeActual. The signed xi-f comparison

  paperQPilotLogVolume C3 <= P.signedHullLogVolume

is equivalent to the exact magnitude comparison

  P.procession.average <= paperQPilotLogMagnitude C3.

The assembly constructs the signed comparison/membership conditionally on
that actual magnitude comparison. The source-theater signed magnitude
comparison itself remains the exact missing theorem; it is not fabricated.
No toy/True/PUnit/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.SignedXiFAssemblyAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeActual
open LeanFormal.IUT.XiFPaper.XiFInequalityProof1
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- The actual source-theater C3 used in PaperThetaMagnitudeActual. -/
noncomputable def sourceTheaterC3
    (D : SourcePilotRegionDonors I) :
    SourcePilotRegionData (l := l) (V := V) I :=
  PaperThetaMagnitudeActual.actualC3 (l := l) (V := V) (I := I) D

/-- The actual signed source-theater PaperSignedHull from PaperSignedHullSignedActual. -/
noncomputable def sourceTheaterSignedHull
    (D : SourcePilotRegionDonors I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) (I := I) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  paperSignedHullFromSignedTheater places tuple mu
    (sourceTheaterC3Signed (K := K) (iota := iota) (W := W)
      (places := places) (tuple := tuple) (mu := mu) (I := I) D) hlog hnormal

/-- Actual signed xi-f comparison data assembled from the two modules. -/
structure SignedXiFSourceData
    (D : SourcePilotRegionDonors I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) (I := I) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average) : Prop where
  magnitude : PaperThetaMagnitudeComparison
    (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)
    (sourceTheaterSignedHull (l := l) (V := V) (I := I) places tuple mu D hlog hnormal)

/-- Signed q-pilot <= signed hull, from the assembled magnitude comparison. -/
theorem signedInequality
    (D : SourcePilotRegionDonors I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) (I := I) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average)
    (S : SignedXiFSourceData places tuple mu D hlog hnormal) :
    paperQPilotLogVolume (sourceTheaterC3Signed (l := l) (V := V) (I := I) D) ≤
      (sourceTheaterSignedHull (l := l) (V := V) (I := I) places tuple mu
        D hlog hnormal).signedHullLogVolume :=
  paperQPilot_le_signedHull_of_thetaMagnitudeComparison
    (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)
    (sourceTheaterSignedHull (l := l) (V := V) (I := I) places tuple mu
      D hlog hnormal) S.magnitude

/-- Signed ray membership, from the same assembled comparison. -/
theorem signedMembership
    (D : SourcePilotRegionDonors I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) (I := I) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average)
    (S : SignedXiFSourceData places tuple mu D hlog hnormal) :
    paperQPilotLogVolume (sourceTheaterC3Signed (l := l) (V := V) (I := I) D) ∈
      hullLogVolumeRay
        (sourceTheaterSignedHull (l := l) (V := V) (I := I) places tuple mu
          D hlog hnormal).signedHullLogVolume :=
  mem_hullLogVolumeRay_iff.mpr
    (signedInequality (l := l) (V := V) (I := I) places tuple mu D hlog hnormal S)

/-- Exact missing source theorem: the signed source-theater magnitude comparison. This is the only unproved comparison field of SignedXiFSourceData. -/
def MissingSourceTheaterSignedMagnitudeComparison
    (D : SourcePilotRegionDonors I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) (I := I) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average) : Prop :=
  PaperThetaMagnitudeComparison
    (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)
    (sourceTheaterSignedHull (l := l) (V := V) (I := I) places tuple mu
      D hlog hnormal)

theorem sourceTheaterSignedMagnitudeComparison_iff
    (D : SourcePilotRegionDonors I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) (I := I) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average) :
    MissingSourceTheaterSignedMagnitudeComparison
      (l := l) (V := V) (I := I) places tuple mu D hlog hnormal ↔
      PaperThetaMagnitudeComparison
        (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)
        (sourceTheaterSignedHull (l := l) (V := V) (I := I) places tuple mu
          D hlog hnormal) := Iff.rfl

#check SignedXiFSourceData
#check signedInequality
#check signedMembership
#check MissingSourceTheaterSignedMagnitudeComparison

end LeanFormal.IUT.XiFPaper.SignedXiFAssemblyAdapted

end
