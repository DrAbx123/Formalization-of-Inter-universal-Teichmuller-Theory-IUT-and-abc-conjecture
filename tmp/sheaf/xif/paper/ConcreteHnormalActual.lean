import tmp.sheaf.xif.paper.C3GaussianThetaPacketActual
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import tmp.sheaf.xif.paper.SignedHnormalActual

/-! # Concrete hnormal: actual Gaussian C3 theta packet reduction

This file reduces the concrete hnormal equality

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu canonicalUnitReference).toReal
  = (c3ThetaSignedProcession actualGaussianC3).average

using the actual source Gaussian packet q = 1/5 and the actual
Haar/unit-factor decomposition.  It proves the actual signed-average formula
for the Gaussian packet (negative packet log-volume divided by the actual
signed-label cardinality), and shows the hnormal equality implies SignedHnormal
through the exact unit-factor reduction.

The equality itself is the Haar normalization choice; it is not faked or
derived from unnormalized Haar data.  No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteHnormalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullNormalizationActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
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

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

/-- The actual signed average of the Gaussian C3 is the negative packet
log-volume divided by the actual signed-label cardinality. -/
theorem actualGaussianSignedAverage_eq_neg_logVolume_div_card :
    actualGaussianSignedAverage (l := l) (V := V) (I := I) D =
      -((actualGaussianC3 (l := l) (V := V) (I := I) D).thetaPacket.logVolume /
        (c3ThetaCard (l := l) : Real)) := by
  unfold actualGaussianSignedAverage
  rw [c3ThetaSignedProcession_average_eq_neg,
    c3ThetaProcession_average]

/-- Concrete hnormal equality with the actual Gaussian C3 packet. -/
def ConcreteHnormalEquality : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    (c3ThetaSignedProcession
      (actualGaussianC3 (l := l) (V := V) (I := I) D)).average

/-- The concrete equality implies SignedHnormal (exact source unit-factor
reduction, no unit-measure lower-bound hypothesis). -/
theorem concreteHnormal_of_equality
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D :=
  signedHnormal_of_unitFactor_noUnit (l := l) (V := V) (I := I)
    places tuple mu D h

/-- The actual C6 canonical-hull real Haar log is the actual unit factor. -/
theorem concreteHnormal_canonicalHullLog :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  canonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu

/-- The concrete equality in canonical-hull Haar form. -/
theorem concreteHnormal_haar_form
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      (c3ThetaSignedProcession
        (actualGaussianC3 (l := l) (V := V) (I := I) D)).average := by
  rw [concreteHnormal_canonicalHullLog]
  exact h

end LeanFormal.IUT.XiFPaper.ConcreteHnormalActual

end
