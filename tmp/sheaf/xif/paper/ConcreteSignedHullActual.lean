import tmp.sheaf.xif.paper.NormalizedHaarHnormalActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.ConcreteC3DonorActual

/-! # Concrete signed PaperSignedHull from the normalized Haar measure

Using the actual normalized Haar measure of NormalizedHaarHnormalActual (the
paper Haar normalization choice) and the actual signed source-theater C3/Gaussian
theta packet, this file constructs the actual PaperSignedHull with its hnormal
field proved.

The C3 root/tensor fields are supplied through the exact actual donor input
SourcePilotRegionDonors; ConcreteC3ActualFields supplies p/place/q/qUnit/theta
but not roots/tensor.  No fake root/tensor data is introduced: the donor
D is the explicit input interface.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteSignedHullActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ConcreteHnormalActual
open LeanFormal.IUT.XiFPaper.NormalizedHaarHnormalActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
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

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

/-- The actual normalized Haar measure (paper normalization choice). -/
noncomputable abbrev concreteNormalizedHaarMeasure :
    Measure (ArithmeticTensorTupleBlock places tuple) :=
  normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu

/-- The normalized measure is additive Haar. -/
instance concreteNormalizedHaarMeasure_isAddHaar :
    Measure.IsAddHaarMeasure
      (concreteNormalizedHaarMeasure (l := l) (V := V) (I := I)
        places tuple D nu) :=
  normalizedHaarMeasure_isAddHaar (l := l) (V := V) (I := I) places tuple D nu

/-- The actual hnormal field for the normalized measure. -/
theorem concreteSignedHnormal :
    SignedHnormal (l := l) (V := V) (I := I) places tuple
      (concreteNormalizedHaarMeasure (l := l) (V := V) (I := I)
        places tuple D nu) D :=
  normalizedHaarMeasure_signedHnormal (l := l) (V := V) (I := I)
    places tuple D nu

/-- The actual signed source-theater C3 equals the Gaussian-packet C3. -/
theorem actualSignedC3_eq_gaussian :
    actualSignedC3 (l := l) (V := V) (I := I) D =
      actualGaussianC3 (l := l) (V := V) (I := I) D := rfl

/-- The actual PaperSignedHull from the normalized Haar measure and actual
source-theater C3/Gaussian theta packet. -/
noncomputable def concretePaperSignedHull :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  actualSignedHull (l := l) (V := V) (I := I) places tuple
    (concreteNormalizedHaarMeasure (l := l) (V := V) (I := I)
      places tuple D nu) D
    (concreteSignedHnormal (l := l) (V := V) (I := I) places tuple D nu)

/-- The concrete PaperSignedHull carries the actual signed source-theater
procession. -/
theorem concretePaperSignedHull_procession :
    (concretePaperSignedHull (l := l) (V := V) (I := I) places tuple D nu).procession =
      c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D) :=
  rfl

/-- The hnormal field of the constructed PaperSignedHull is the actual C6 Haar
comparison. -/
theorem concretePaperSignedHull_hnormal :
    (concretePaperSignedHull (l := l) (V := V) (I := I) places tuple D nu).ambient.logVolume
        (concretePaperSignedHull (l := l) (V := V) (I := I) places tuple D nu).ambient.hull =
      ENNReal.ofReal
        (c3ThetaSignedProcession
          (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
  rfl

end LeanFormal.IUT.XiFPaper.ConcreteSignedHullActual

end
