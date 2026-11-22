import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on hlog and hnormal. Signed procession/average nonnegativity/containment are actual, but the C6 Haar/theta hnormal identity is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# PaperSignedHull with the nonnegative signed theta procession

The unsigned C3 procession has values log(C3.thetaPacket.scale j), which are
negative in the source q = 1/5 direction. This file defines the signed
procession

  c3ThetaSignedProcession C3

with values -log(C3.thetaPacket.scale j) and the same uniform finite weights,
proves its average is nonnegative under the exact sign field

  hlog : C3.thetaPacket.logVolume <= 0,

and builds the finite hull and PaperSignedHull from these actual signed values.
The finite-hull containment is proved from the absolute-value sum, not assumed.

The only remaining Haar field is

  hnormal : actual C6 iqInterface.logVolume iqInterface.hull
    = ENNReal.ofReal (c3ThetaSignedProcession C3).average,

kept explicit as the exact missing C6/Haar comparison.

No toy data, forbidden declaration, axiom, or unfilled proof is used.
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

/-- The actual C6 IQ carrier. -/
abbrev PaperC6Carrier (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i) : Type (max ua uv) :=
  C6IQCarrier places tuple

/-- The signed (nonnegative-direction) theta procession: values are the
negatives of the actual packet log-scales. -/
noncomputable def c3ThetaSignedProcession
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    WeightedValues (SignedLabel l.value) where
  value j := -Real.log (C3.thetaPacket.scale j)
  weight _ := (c3ThetaCard (l := l) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (c3ThetaCard (l := l) : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (c3ThetaCard_pos (l := l)))
    exact (mul_inv_cancel₀ hcard).symm

/-- Signed procession weights are nonnegative. -/
theorem c3ThetaSignedProcession_weights_nonnegative
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (j : SignedLabel l.value) :
    0 <= (c3ThetaSignedProcession C3).weight j := by
  unfold c3ThetaSignedProcession
  exact inv_nonneg.mpr (Nat.cast_nonneg (c3ThetaCard (l := l)))

/-- The signed procession average is the negative of the unsigned one. -/
theorem c3ThetaSignedProcession_average_eq_neg
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    (c3ThetaSignedProcession C3).average = -(c3ThetaProcession C3).average := by
  unfold WeightedValues.average c3ThetaSignedProcession c3ThetaProcession
  simp only [Finset.sum_neg_distrib, mul_neg, neg_div]

/-- Exact sign field: the actual theta packet log-volume is nonpositive. -/
def ThetaPacketLogVolumeNonpos
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  C3.thetaPacket.logVolume <= 0

/-- Under the exact packet sign field, the signed procession has nonnegative
average. -/
theorem c3ThetaSignedProcession_average_nonneg
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos C3) :
    0 <= (c3ThetaSignedProcession C3).average := by
  have hu : (c3ThetaProcession C3).average <= 0 := by
    rw [c3ThetaProcession_average]
    exact div_nonpos_of_nonpos_of_nonneg hlog
      (Nat.cast_nonneg (c3ThetaCard (l := l)))
  rw [c3ThetaSignedProcession_average_eq_neg]
  exact neg_nonneg.mpr hu

/-- Finite hull attached to the actual signed procession: values are the signed
packet log-scales, hullVolume is the sum of their absolute values. -/
noncomputable def signedSourceTheaterFiniteHull
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    FiniteHull (SignedLabel l.value) where
  volume j := (c3ThetaSignedProcession C3).value j
  hullVolume := Finset.sum Finset.univ
    (fun j : SignedLabel l.value => |(c3ThetaSignedProcession C3).value j|)
  contains j := by
    calc
      (c3ThetaSignedProcession C3).value j <=
          |(c3ThetaSignedProcession C3).value j| := le_abs_self _
      _ <= Finset.sum Finset.univ
            (fun i : SignedLabel l.value =>
              |(c3ThetaSignedProcession C3).value i|) :=
        Finset.single_le_sum
          (fun i _ => abs_nonneg ((c3ThetaSignedProcession C3).value i))
          (Finset.mem_univ j)

/-- Actual PaperSignedHull with the signed nonnegative procession, conditional
on the exact packet sign field and the exact C6 Haar comparison. -/
noncomputable def paperSignedHullFromSignedTheater
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos C3)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal (c3ThetaSignedProcession C3).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) where
  ambient := (C6ActualIQData.actual places tuple mu).iqInterface
  procession := c3ThetaSignedProcession C3
  hull := signedSourceTheaterFiniteHull (I := I) C3
  weighted_matches_hull := by
    intro j
    rfl
  weights_nonnegative := c3ThetaSignedProcession_weights_nonnegative C3
  average_nonneg := c3ThetaSignedProcession_average_nonneg C3 hlog
  hull_logVolume_eq_average := hnormal

/-- The constructed signed paper hull carries exactly the signed procession. -/
theorem paperSignedHullFromSignedTheater_procession_eq
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos C3)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal (c3ThetaSignedProcession C3).average) :
    (paperSignedHullFromSignedTheater (I := I) places tuple mu C3 hlog hnormal).procession =
      c3ThetaSignedProcession C3 :=
  rfl

/-- Exact source-theater C3. -/
noncomputable def sourceTheaterC3Signed
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    SourcePilotRegionData (l := l) (V := V) I :=
  c3WithSourceTheaterTheta I D

/-- Signed source-theater PaperSignedHull. -/
noncomputable def sourceTheaterSignedPaperSignedHull
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hlog : ThetaPacketLogVolumeNonpos
      (sourceTheaterC3Signed (l := l) (V := V) D))
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        ENNReal.ofReal
          (c3ThetaSignedProcession
            (sourceTheaterC3Signed (l := l) (V := V) D)).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  paperSignedHullFromSignedTheater (I := I) places tuple mu
    (sourceTheaterC3Signed (l := l) (V := V) D) hlog hnormal

end LeanFormal.IUT.XiFPaper

end
