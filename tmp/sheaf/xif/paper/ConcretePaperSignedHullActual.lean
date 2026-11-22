import tmp.sheaf.xif.paper.ConcreteHnormalActual
import tmp.sheaf.xif.paper.C3GaussianThetaPacketActual
import tmp.sheaf.n8.closure.C3Actual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.PaperSignedHullNormalizationActual
import tmp.sheaf.xif.paper.ConcreteHnormalActual

/-!
# Concrete actual PaperSignedHull

This file constructs the actual signed PaperSignedHull from the concrete C3
data, using the actual C6 IQ carrier and the concrete Haar normalization
interface of `ConcreteHnormalActual`.

The only input is the exact concrete hnormal equality

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu canonicalUnitReference).toReal
  = (c3ThetaSignedProcession actualSignedC3).average,

which is the explicit Haar normalization choice.  It is not fabricated here:
`ConcreteHnormalActual.concreteHnormal_of_equality` proves the signed
hnormal from it, and the actual signed hull is then constructed by
`PaperThetaMagnitudeSignedActual.actualSignedHull`.

No inequality is judged; no missing-only record is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace ConcretePaperSignedHullActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullNormalizationActual
open LeanFormal.IUT.XiFPaper.ConcreteHnormalActual
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

/-- The actual concrete signed PaperSignedHull, built from the concrete
hnormal equality via the actual C6 IQ data. -/
noncomputable def concretePaperSignedHull
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  actualSignedHull (l := l) (V := V) (I := I) places tuple mu D
    (ConcreteHnormalActual.concreteHnormal_of_equality
      (l := l) (V := V) (I := I) places tuple mu D h)

/-- The constructed concrete signed hull carries exactly the actual signed
theta procession. -/
theorem concretePaperSignedHull_procession_eq
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    (concretePaperSignedHull (l := l) (V := V) (I := I)
      places tuple mu D h).procession =
      c3ThetaSignedProcession (actualSignedC3 (l := l) (V := V) (I := I) D) :=
  actualSignedHull_procession_eq (l := l) (V := V) (I := I) places tuple mu D
    (ConcreteHnormalActual.concreteHnormal_of_equality
      (l := l) (V := V) (I := I) places tuple mu D h)

/-- The constructed concrete signed hull is the actual signed hull at the
proved SignedHnormal. -/
theorem concretePaperSignedHull_eq_actualSignedHull
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    concretePaperSignedHull (l := l) (V := V) (I := I)
        places tuple mu D h =
      actualSignedHull (l := l) (V := V) (I := I) places tuple mu D
        (ConcreteHnormalActual.concreteHnormal_of_equality
          (l := l) (V := V) (I := I) places tuple mu D h) :=
  rfl

/-- The actual hull log-volume equality field of the constructed concrete
signed hull is read directly from the constructed PaperSignedHull. -/
theorem concretePaperSignedHull_hull_logVolume_eq
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).iqInterface.hull =
      ENNReal.ofReal
        (c3ThetaSignedProcession
          (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
  (concretePaperSignedHull (l := l) (V := V) (I := I)
    places tuple mu D h).hull_logVolume_eq_average

/-- The concrete hnormal equality implies the actual signed hnormal used by
the constructed hull. -/
theorem concretePaperSignedHull_signedHnormal
    (h : ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple mu D) :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D :=
  ConcreteHnormalActual.concreteHnormal_of_equality
    (l := l) (V := V) (I := I) places tuple mu D h

end ConcretePaperSignedHullActual
end LeanFormal.IUT.XiFPaper
end
