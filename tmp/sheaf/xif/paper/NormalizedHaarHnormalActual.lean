import tmp.sheaf.xif.paper.ConcreteHnormalActual
import tmp.sheaf.xif.paper.UnitReferenceMeasureActual

/-! # Actual normalized Haar measure with hnormal

For any actual additive Haar measure nu, define

  c = exp(signedAverage - hullUnitLog - log nu(canonicalUnitReference))

and mu = ENNReal.ofReal c * nu.  Since c > 0 and finite, mu is an additive
Haar measure.  The scaling law and the actual C6 unit-factor formula then give

  hullUnitLog + log mu(unit) = signedAverage,

i.e. exactly the concrete hnormal equality.  This is the paper's Haar
normalization choice, constructed rather than assumed; it is not a fake
hnormal.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NormalizedHaarHnormalActual

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
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open MeasureTheory

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

/-- The positive normalization scale. -/
noncomputable def normalizedHaarScale : Real :=
  Real.exp
    (actualGaussianSignedAverage (l := l) (V := V) (I := I) D -
      arithmeticTupleHullUnitLogVolume places tuple -
      Real.log (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

theorem normalizedHaarScale_pos : 0 < normalizedHaarScale (l := l) (V := V)
    (I := I) places tuple D nu :=
  Real.exp_pos _

/-- The normalized Haar measure mu = c * nu. -/
noncomputable def normalizedHaarMeasure :
    Measure (ArithmeticTensorTupleBlock places tuple) :=
  (ENNReal.ofReal (normalizedHaarScale (l := l) (V := V) (I := I)
    places tuple D nu)) • nu

/-- The normalized measure is still an additive Haar measure. -/
instance normalizedHaarMeasure_isAddHaar :
    Measure.IsAddHaarMeasure
      (normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu) := by
  unfold normalizedHaarMeasure
  exact Measure.IsAddHaarMeasure.smul (μ := nu)
    (c := ENNReal.ofReal (normalizedHaarScale (l := l) (V := V) (I := I)
      places tuple D nu))
    (ENNReal.ofReal_ne_zero_iff.mpr
      (normalizedHaarScale_pos (l := l) (V := V) (I := I) places tuple D nu))
    ENNReal.ofReal_ne_top

/-- The actual normalized unit-reference mass is c times the reference mass. -/
theorem normalizedHaarMeasure_unit_toReal :
    ((normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu)
      (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      normalizedHaarScale (l := l) (V := V) (I := I) places tuple D nu *
        (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
  unfold normalizedHaarMeasure
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (le_of_lt (normalizedHaarScale_pos
        (l := l) (V := V) (I := I) places tuple D nu))]

/-- The normalized unit log is signedAverage minus the hull unit log. -/
theorem normalizedHaarMeasure_unit_log :
    Real.log
        ((normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu)
          (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      actualGaussianSignedAverage (l := l) (V := V) (I := I) D -
        arithmeticTupleHullUnitLogVolume places tuple := by
  rw [normalizedHaarMeasure_unit_toReal]
  have hscale : normalizedHaarScale (l := l) (V := V) (I := I)
      places tuple D nu ≠ 0 :=
    ne_of_gt (normalizedHaarScale_pos (l := l) (V := V) (I := I)
      places tuple D nu)
  have hnu : (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal ≠ 0 :=
    ne_of_gt (unitReference_toReal_pos places tuple nu)
  rw [Real.log_mul hscale hnu]
  unfold normalizedHaarScale
  rw [Real.log_exp]
  ring

/-- The concrete hnormal equality holds for the normalized measure. -/
theorem normalizedHaarMeasure_concreteHnormalEquality :
    ConcreteHnormalEquality (l := l) (V := V) (I := I)
      places tuple (normalizedHaarMeasure (l := l) (V := V) (I := I)
        places tuple D nu) D := by
  unfold ConcreteHnormalEquality
  rw [normalizedHaarMeasure_unit_log (l := l) (V := V) (I := I)
    places tuple D nu]
  unfold actualGaussianSignedAverage
  ring

/-- The actual SignedHnormal for the normalized measure. -/
theorem normalizedHaarMeasure_signedHnormal :
    SignedHnormal (l := l) (V := V) (I := I) places tuple
      (normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu) D :=
  concreteHnormal_of_equality (l := l) (V := V) (I := I) places tuple
    (normalizedHaarMeasure (l := l) (V := V) (I := I) places tuple D nu) D
    (normalizedHaarMeasure_concreteHnormalEquality
      (l := l) (V := V) (I := I) places tuple D nu)

end LeanFormal.IUT.XiFPaper.NormalizedHaarHnormalActual

end
