import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringSigned

/-!
# A genuinely signed Step-XI certificate for the actual tuple hull

The `ENNReal`-valued interface path cannot express a negative log-volume: it
encodes `q` and `theta` through `ENNReal.ofReal`, which is `0` on negative
inputs.  This file uses instead the real signed Haar logs of
`FinitePlaceIQHullSignedLogVolume`:

* `qSigned` is the actual signed hull log `log (mu hull)`;
* `thetaSigned` is the actual signed unit-region log `log (mu unitRegion)`;
* `q_le_hull` is reflexivity;
* `hull_le_theta` is the genuine inclusion inequality `log (mu hull) <=
  log (mu unitRegion)`.

The certificate is non-vacuous under the normalization `mu unitRegion = 1`
and the strict bound `mu hull < 1`, which make both signed logs negative.
No source `1,circ U` construction or source q comparison is claimed.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

universe u v w uL

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- Constant weighted values with value `hullLog` and weight `1`. -/
def arithmeticTupleSignedWeightedValues
    (label : Type uL) [Fintype label] [Nonempty label] (hullLog : Real) :
    WeightedValues label where
  value := fun _ => hullLog
  weight := fun _ => 1
  weightTotal := (Fintype.card label : Real)
  weightTotal_pos := by
    exact_mod_cast Fintype.card_pos
  weightTotal_eq_sum := by
    simp

/-- The signed finite hull: every labeled volume and the hull volume are the
signed hull log. -/
def arithmeticTupleSignedFiniteHull
    (label : Type uL) [Fintype label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] : FiniteHull label where
  volume := fun _ => arithmeticTupleCanonicalHullHaarLog places tuple μ
  hullVolume := arithmeticTupleCanonicalHullHaarLog places tuple μ
  contains := fun _ => le_rfl

theorem arithmeticTupleSignedFiniteHull_hullVolume
    (label : Type uL) [Fintype label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFiniteHull places tuple label μ).hullVolume =
      arithmeticTupleCanonicalHullHaarLog places tuple μ := rfl

/-- The signed certificate with actual negative log-volumes.  The hypothesis
`hullLog < 0` is the strict form of `mu hull < 1` under the normalization
`mu unitRegion = 1`. -/
def arithmeticTupleSignedFiniteCertificate
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hneg : arithmeticTupleCanonicalHullHaarLog places tuple μ < 0) :
    StepXIFiniteCertificateSigned label where
  hull := arithmeticTupleSignedFiniteHull places tuple label μ
  weighted := arithmeticTupleSignedWeightedValues label
    (arithmeticTupleCanonicalHullHaarLog places tuple μ)
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := fun _ => by
    simp [arithmeticTupleSignedWeightedValues]
  qSigned := arithmeticTupleCanonicalHullHaarLog places tuple μ
  thetaSigned := arithmeticTupleIQHullUnitRegionHaarLog places tuple μ
  q_le_hull := by
    rw [arithmeticTupleSignedFiniteHull_hullVolume]
  hull_le_theta := by
    simpa [arithmeticTupleSignedFiniteHull] using
      arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog places tuple μ
  q_negative := hneg

theorem arithmeticTupleSignedFiniteCertificate_thetaSigned
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hneg : arithmeticTupleCanonicalHullHaarLog places tuple μ < 0) :
    (arithmeticTupleSignedFiniteCertificate places tuple label μ hneg).thetaSigned =
      arithmeticTupleIQHullUnitRegionHaarLog places tuple μ := rfl

/-- Link evidence with the unit-region signed log as target. -/
def arithmeticTupleSignedLinkEvidence
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hneg : arithmeticTupleCanonicalHullHaarLog places tuple μ < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    SignedFiniteStepXILinkEvidence
      (arithmeticTupleSignedFiniteCertificate places tuple label μ hneg) where
  targetSigned := arithmeticTupleIQHullUnitRegionHaarLog places tuple μ
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target :=
    by
      simpa [arithmeticTupleSignedFiniteCertificate, arithmeticTupleSignedFiniteHull] using
        arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog places tuple μ
  target_le_theta := by
    rw [arithmeticTupleSignedFiniteCertificate_thetaSigned]

/-- Corollary 3.12 conclusion from the genuinely signed certificate.  The
conclusion `qSigned <= thetaSigned` is the real log-volume comparison, not the
sign-blind `ofReal` conclusion. -/
theorem arithmeticTupleSignedCor312Conclusion
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hneg : arithmeticTupleCanonicalHullHaarLog places tuple μ < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((arithmeticTupleSignedFiniteCertificate places tuple label μ hneg).toContract
        (arithmeticTupleSignedLinkEvidence places tuple label μ hneg
          ipl she apt hipl hshe hapt)) :=
  cor312_of_signed_finite_certificate
    (arithmeticTupleSignedFiniteCertificate places tuple label μ hneg)
    (arithmeticTupleSignedLinkEvidence places tuple label μ hneg
      ipl she apt hipl hshe hapt)

end

end LeanFormal.IUT.NumberFieldFinitePlace
