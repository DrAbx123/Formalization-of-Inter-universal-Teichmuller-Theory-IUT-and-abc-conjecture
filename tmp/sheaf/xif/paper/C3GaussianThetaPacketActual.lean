import tmp.sheaf.xif.paper.PaperSignedHullNormalizationActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import tmp.sheaf.xif.paper.PaperSignedHullNormalizationActual
import tmp.sheaf.xif.paper.SignedHnormalActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.n8.closure.C3Actual

/-! # Actual Gaussian C3 theta packet and Haar/hull normalization equality

The source theater has the actual finite Gaussian theta packet
FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos, with q = 1/5.
This is the actual source q/Gaussian packet, not a donor parameter.  We package
it as a C3 theta packet by c3WithSourceTheaterTheta and state the paper-side
Haar/hull normalization equality for that actual C3.

Paper-side equality (hnormal):

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu canonicalUnitReference).toReal
  = (c3ThetaSignedProcession actualGaussianC3).average.

This file constructs the actual packet and actual C3 and proves the packet
q/scales.  It does not fake hnormal: PaperSignedHullNormalizationActual proves
hnormal follows from this equality, and the equality itself is the exact Haar
normalization choice, not a consequence of the unnormalized Haar data.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullNormalizationActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

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

variable (D : SourcePilotRegionDonors I)

/-- The actual source Gaussian theta packet: q is the actual local q-parameter
norm 1/5. -/
noncomputable def actualGaussianThetaPacket : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos

@[simp] theorem actualGaussianThetaPacket_q :
    (actualGaussianThetaPacket (l := l)).q = gaussianFiveThetaQ := rfl

theorem actualGaussianThetaPacket_q_eq_inv_five :
    (actualGaussianThetaPacket (l := l)).q = (5 : Real)⁻¹ := by
  rw [actualGaussianThetaPacket_q, gaussianFiveThetaQ_eq_inv_five]

theorem actualGaussianThetaPacket_q_lt_one :
    (actualGaussianThetaPacket (l := l)).q < 1 := by
  rw [actualGaussianThetaPacket_q_eq_inv_five]
  norm_num

/-- The actual source-theater Gaussian packet is exactly the source theater
theta packet. -/
theorem actualGaussianThetaPacket_eq_sourceTheater :
    actualGaussianThetaPacket (l := l) = (sourceTheater l).thetaPacket :=
  (sourceTheater_thetaPacket l).symm

/-- The actual C3 with the source Gaussian theta packet. -/
noncomputable def actualGaussianC3 : SourcePilotRegionData (l := l) (V := V) I :=
  c3WithSourceTheaterTheta (I := I) D

theorem actualGaussianC3_thetaPacket :
    (actualGaussianC3 (l := l) (V := V) (I := I) D).thetaPacket =
      actualGaussianThetaPacket (l := l) :=
  c3WithSourceTheaterTheta_thetaPacket (I := I) D

/-- The actual signed theta procession average of the Gaussian C3. -/
noncomputable def actualGaussianSignedAverage : Real :=
  (c3ThetaSignedProcession (actualGaussianC3 (l := l) (V := V) (I := I) D)).average

/-- The exact paper-side Haar/hull normalization equality for the actual
Gaussian C3.  This is the hnormal equality; it is not fabricated. -/
def GaussianC3HaarNormalizationEquality : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    actualGaussianSignedAverage (l := l) (V := V) (I := I) D

/-- The exact normalization equality supplies SignedHnormal for the Gaussian C3. -/
theorem gaussianC3_hnormal_of_normalization
    (h : GaussianC3HaarNormalizationEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D :=
  signedHnormal_of_unitFactor_noUnit (l := l) (V := V) (I := I)
    places tuple mu D h

/-- The actual Gaussian theta packet has q = 1/5, so the signed procession is
the actual contracting source procession. -/
theorem actualGaussianC3_thetaPacket_q_eq_inv_five :
    (actualGaussianC3 (l := l) (V := V) (I := I) D).thetaPacket.q =
      (5 : Real)⁻¹ := by
  rw [actualGaussianC3_thetaPacket, actualGaussianThetaPacket_q_eq_inv_five]

end LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual

end
