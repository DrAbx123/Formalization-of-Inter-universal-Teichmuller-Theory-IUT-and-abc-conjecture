import tmp.sheaf.xif.paper.PaperSignedHullSignedActual

/-!
# PaperProcessionEq for the signed source-theater paper hull

PaperProcessionEqC3ThetaProcession is defined by
  P.procession = c3ThetaProcession C3,
where c3ThetaProcession is the unsigned packet procession with values
Real.log(C3.thetaPacket.scale j).

The source-theater PaperSignedHull built in PaperSignedHullSignedActual has the
signed procession c3ThetaSignedProcession with values
-Real.log(C3.thetaPacket.scale j). Therefore its procession equality is exactly
the missing sign identification

  SignedUnsignedProcessionEq C3 :
    c3ThetaSignedProcession C3 = c3ThetaProcession C3,

i.e. all packet log-scales vanish. That equality is not a source-theater fact:
it forces C3.thetaPacket.logVolume = 0, while the constructed source-theater C3
only fixes q = 1/5 and no theorem rules out nonzero theta log-scales.

This file proves the exact reduction and the consequences of the missing
equality. It does not assert the equality. No toy data, forbidden declaration,
forbidden declaration, or unfilled proof is used.
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
open LeanFormal.IUT.ProcessionThetaPacketAverageActual
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

/-- Exact missing sign identification: the signed theta procession equals the
unsigned theta procession. -/
def SignedUnsignedProcessionEq
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  c3ThetaSignedProcession C3 = c3ThetaProcession C3

/-- The missing sign equality forces every packet log-scale to vanish. -/
theorem signedUnsignedProcessionEq_log_eq_zero
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : SignedUnsignedProcessionEq C3) (j : SignedLabel l.value) :
    Real.log (C3.thetaPacket.scale j) = 0 := by
  have hv := congrArg
    (fun w : WeightedValues (SignedLabel l.value) => w.value j) h
  simp only [c3ThetaSignedProcession, c3ThetaProcession] at hv
  linarith

/-- The missing sign equality forces the actual theta packet log-volume to
vanish. -/
theorem signedUnsignedProcessionEq_packetLogVolume_eq_zero
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : SignedUnsignedProcessionEq C3) :
    C3.thetaPacket.logVolume = 0 := by
  rw [C3.thetaPacket.logVolume_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact signedUnsignedProcessionEq_log_eq_zero C3 h j

/-- The source-theater signed PaperSignedHull. -/
noncomputable def signedProcessionSourceHull
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) I D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) I D)).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  sourceTheaterSignedPaperSignedHull (l := l) (V := V) (I := I)
    places tuple mu D hlog hnormal

/-- Exact reduction of PaperProcessionEqC3ThetaProcession for the signed
source-theater hull: it is equivalent to the missing sign identification. -/
theorem signedProcessionSourceHull_paperProcessionEq_iff
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) I D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) I D)).average) :
    PaperProcessionEqC3ThetaProcession
        (l := l) (sourceTheaterC3Signed (l := l) (V := V) I D)
        (signedProcessionSourceHull (l := l) (V := V) (I := I)
          places tuple mu D hlog hnormal) <->
      SignedUnsignedProcessionEq
        (sourceTheaterC3Signed (l := l) (V := V) I D) :=
  Iff.rfl

/-- Conditional proof: under the exact missing sign identification,
PaperProcessionEqC3ThetaProcession holds for the signed source-theater hull. -/
theorem signedProcessionSourceHull_paperProcessionEq_of_signedUnsigned
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) I D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) I D)).average)
    (hsign : SignedUnsignedProcessionEq
      (sourceTheaterC3Signed (l := l) (V := V) I D)) :
    PaperProcessionEqC3ThetaProcession
      (l := l) (sourceTheaterC3Signed (l := l) (V := V) I D)
      (signedProcessionSourceHull (l := l) (V := V) (I := I)
        places tuple mu D hlog hnormal) :=
  (signedProcessionSourceHull_paperProcessionEq_iff (l := l) (V := V) (I := I)
    places tuple mu D hlog hnormal).mpr hsign

end LeanFormal.IUT.XiFPaper

end
