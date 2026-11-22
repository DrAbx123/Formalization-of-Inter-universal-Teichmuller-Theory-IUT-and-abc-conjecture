import tmp.sheaf.xif.paper.ConcretePaperSignedHullActual
import tmp.sheaf.xif.paper.NormalizedHaarHnormalActual
import tmp.sheaf.xif.paper.C3GaussianThetaPacketActual
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.xif.paper.SignedHnormalActual

/-!
# Unconditional concrete PaperSignedHull via the normalized Haar measure

The concrete hnormal equality is not assumed here.  For any actual additive Haar
measure `nu`, `NormalizedHaarHnormalActual.normalizedHaarMeasure` is the
paper's normalization choice `c * nu`, and its concrete hnormal equality is
proved.  Feeding that proof to `ConcretePaperSignedHullActual` gives an
unconditional actual PaperSignedHull on the concrete C3 data.

The construction identifies the concrete Gaussian C3 with the actual signed C3;
both are `c3WithSourceTheaterTheta I D`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace ConcreteSignedHullUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ConcreteHnormalActual
open LeanFormal.IUT.XiFPaper.NormalizedHaarHnormalActual
open LeanFormal.IUT.XiFPaper.ConcretePaperSignedHullActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
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
variable (D : SourcePilotRegionDonors I)
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

/-- The concrete Gaussian C3 is definitionally the actual signed C3. -/
theorem actualGaussianC3_eq_actualSignedC3 :
    actualGaussianC3 (l := l) (V := V) (I := I) D =
      actualSignedC3 (l := l) (V := V) (I := I) D :=
  rfl

/-- The concrete Gaussian signed average is the actual signed average. -/
theorem actualGaussianSignedAverage_eq_actualSignedAverage :
    actualGaussianSignedAverage (l := l) (V := V) (I := I) D =
      (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average := by
  unfold actualGaussianSignedAverage
  rw [actualGaussianC3_eq_actualSignedC3]

/-- Unconditional actual PaperSignedHull using the paper-normalized Haar
measure `normalizedHaarMeasure nu`. -/
noncomputable def unconditionalPaperSignedHull :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  concretePaperSignedHull (l := l) (V := V) (I := I) places tuple
    (normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu) D
    (normalizedHaarMeasure_concreteHnormalEquality
      (l := l) (V := V) (I := I) places tuple D nu)

/-- The unconditional hull carries the actual signed theta procession. -/
theorem unconditionalPaperSignedHull_procession_eq :
    (unconditionalPaperSignedHull (l := l) (V := V) (I := I)
      places tuple D nu).procession =
      c3ThetaSignedProcession (actualSignedC3 (l := l) (V := V) (I := I) D) :=
  concretePaperSignedHull_procession_eq (l := l) (V := V) (I := I)
    places tuple (normalizedHaarMeasure (l := l) (V := V) (I := I)
      places tuple D nu) D
    (normalizedHaarMeasure_concreteHnormalEquality
      (l := l) (V := V) (I := I) places tuple D nu)

/-- The unconditional hull's C6 log-volume equals the actual signed average. -/
theorem unconditionalPaperSignedHull_hull_logVolume_eq :
    (C6ActualIQData.actual places tuple
        (normalizedHaarMeasure (l := l) (V := V) (I := I)
          places tuple D nu)).iqInterface.logVolume
        (C6ActualIQData.actual places tuple
          (normalizedHaarMeasure (l := l) (V := V) (I := I)
            places tuple D nu)).iqInterface.hull =
      ENNReal.ofReal
        (c3ThetaSignedProcession
          (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
  concretePaperSignedHull_hull_logVolume_eq (l := l) (V := V) (I := I)
    places tuple (normalizedHaarMeasure (l := l) (V := V) (I := I)
      places tuple D nu) D
    (normalizedHaarMeasure_concreteHnormalEquality
      (l := l) (V := V) (I := I) places tuple D nu)

/-- The actual SignedHnormal for the normalized measure used by the
unconditional hull. -/
theorem unconditionalPaperSignedHull_signedHnormal :
    SignedHnormal (l := l) (V := V) (I := I) places tuple
      (normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu) D :=
  normalizedHaarMeasure_signedHnormal (l := l) (V := V) (I := I)
    places tuple D nu

end ConcreteSignedHullUnconditionalActual
end LeanFormal.IUT.XiFPaper
end
