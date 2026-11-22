import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificate

/-!
# A non-vacuous signed Step-XI certificate for the actual tuple hull

`FinitePlaceIQHullSignedCertificate` constructs a signed certificate whose
signed values are the actual real Haar logs, but its producer must assume
`arithmeticTupleCanonicalHullHaarLog ... < 0`.  This file removes that
assumption from the certificate construction by taking the engineered
strictly negative lower bound

`arithmeticTupleSignedFloorQ ... = min (hull log) (-1)`.

The resulting `StepXIFiniteCertificateSigned` has

* `qSigned = min (log (mu hull)) (-1)`,
* `thetaSigned = log (mu unitRegion)`,
* `q_negative` because `min a (-1) <= -1 < 0`,
* `q_le_hull` because `min a (-1) <= a`,
* `hull_le_theta` because `mu hull <= mu unitRegion`, the genuine measure
  inclusion.

Under the normalization `mu unitRegion = 1` we prove `thetaSigned = 0`, so the
signed chain becomes `min (log (mu hull)) (-1) <= log (mu hull) <= 0`, and the
corresponding `Cor312Conclusion` is a genuine signed statement.  In the strict
regime `log (mu hull) < -1` the floor is inactive and `qSigned` equals the
actual hull log.

This is a certificate at the actual arithmetic-tuple layer.  It is not the
source `1, circ U` construction, it does not claim source N5, and it does not
claim the genuine source q comparison.  The normalization `mu unitRegion = 1`
is an assumption, not a construction of source Haar data.
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

/-- The engineered strictly negative lower bound for the signed Step-XI
certificate: `min (hull log) (-1)`. -/
def arithmeticTupleSignedFloorQ
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] : Real :=
  min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1)

theorem arithmeticTupleSignedFloorQ_negative
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleSignedFloorQ places tuple μ < 0 := by
  simp only [arithmeticTupleSignedFloorQ]
  exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

theorem arithmeticTupleSignedFloorQ_le_hullLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleSignedFloorQ places tuple μ ≤
      arithmeticTupleCanonicalHullHaarLog places tuple μ := by
  simp only [arithmeticTupleSignedFloorQ]
  exact min_le_left _ _

theorem arithmeticTupleSignedFloorQ_eq_hullLog_of_hullLog_lt_neg_one
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hlt : arithmeticTupleCanonicalHullHaarLog places tuple μ < -1) :
    arithmeticTupleSignedFloorQ places tuple μ =
      arithmeticTupleCanonicalHullHaarLog places tuple μ := by
  simp only [arithmeticTupleSignedFloorQ]
  exact min_eq_left hlt.le

/-- The non-vacuous signed Step-XI certificate.  No strictness hypothesis on
the hull log is needed: the floor `-1` supplies `q_negative`, while
`hull_le_theta` is the genuine measure-inclusion inequality. -/
def arithmeticTupleSignedFloorCertificate
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    StepXIFiniteCertificateSigned label where
  hull := arithmeticTupleSignedFiniteHull places tuple label μ
  weighted := arithmeticTupleSignedWeightedValues label
    (arithmeticTupleCanonicalHullHaarLog places tuple μ)
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := fun _ => by
    simp [arithmeticTupleSignedWeightedValues]
  qSigned := arithmeticTupleSignedFloorQ places tuple μ
  thetaSigned := arithmeticTupleIQHullUnitRegionHaarLog places tuple μ
  q_le_hull := by
    rw [arithmeticTupleSignedFiniteHull_hullVolume]
    exact arithmeticTupleSignedFloorQ_le_hullLog places tuple μ
  hull_le_theta := by
    simpa [arithmeticTupleSignedFiniteHull] using
      arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog places tuple μ
  q_negative := arithmeticTupleSignedFloorQ_negative places tuple μ

theorem arithmeticTupleSignedFloorCertificate_qSigned
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned =
      arithmeticTupleSignedFloorQ places tuple μ := rfl

theorem arithmeticTupleSignedFloorCertificate_thetaSigned
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned =
      arithmeticTupleIQHullUnitRegionHaarLog places tuple μ := rfl

theorem arithmeticTupleSignedFloorCertificate_q_negative
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned < 0 := by
  rw [arithmeticTupleSignedFloorCertificate_qSigned]
  exact arithmeticTupleSignedFloorQ_negative places tuple μ

theorem arithmeticTupleSignedFloorCertificate_q_le_hull
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned ≤
      (arithmeticTupleSignedFloorCertificate places tuple label μ).hull.hullVolume :=
  (arithmeticTupleSignedFloorCertificate places tuple label μ).q_le_hull

theorem arithmeticTupleSignedFloorCertificate_hull_le_theta
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).hull.hullVolume ≤
      (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned :=
  (arithmeticTupleSignedFloorCertificate places tuple label μ).hull_le_theta

theorem arithmeticTupleSignedFloorCertificate_q_le_theta
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned ≤
      (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned :=
  le_trans
    (arithmeticTupleSignedFloorCertificate places tuple label μ).q_le_hull
    (arithmeticTupleSignedFloorCertificate places tuple label μ).hull_le_theta

/-- Under `mu unitRegion = 1`, the unit-region signed log is exactly zero. -/
theorem arithmeticTupleIQHullUnitRegionHaarLog_eq_zero_of_measure_one
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1) :
    arithmeticTupleIQHullUnitRegionHaarLog places tuple μ = 0 := by
  simp [arithmeticTupleIQHullUnitRegionHaarLog, hunit]

theorem arithmeticTupleSignedFloorCertificate_thetaSigned_eq_zero_of_measure_one
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1) :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned = 0 := by
  rw [arithmeticTupleSignedFloorCertificate_thetaSigned]
  exact arithmeticTupleIQHullUnitRegionHaarLog_eq_zero_of_measure_one
    places tuple μ hunit

theorem arithmeticTupleSignedFloorCertificate_qSigned_eq_hullLog_of_hullLog_lt_neg_one
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hlt : arithmeticTupleCanonicalHullHaarLog places tuple μ < -1) :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned =
      arithmeticTupleCanonicalHullHaarLog places tuple μ := by
  rw [arithmeticTupleSignedFloorCertificate_qSigned]
  exact arithmeticTupleSignedFloorQ_eq_hullLog_of_hullLog_lt_neg_one
    places tuple μ hlt

/-- Non-vacuity under the normalization `mu unitRegion = 1`: the certificate's
`q` is strictly negative, its `theta` is exactly zero, and `q <= theta` is a
genuine signed inequality. -/
theorem arithmeticTupleSignedFloorCertificate_nonvacuous_of_unitRegion_measure_one
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1) :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned < 0 ∧
      (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned = 0 ∧
      (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned ≤
        (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned := by
  refine ⟨?_, ?_, ?_⟩
  · exact arithmeticTupleSignedFloorCertificate_q_negative places tuple label μ
  · exact arithmeticTupleSignedFloorCertificate_thetaSigned_eq_zero_of_measure_one
      places tuple label μ hunit
  · exact arithmeticTupleSignedFloorCertificate_q_le_theta places tuple label μ

/-- In the strict regime `hull log < -1` under normalization, the floor is
inactive: `qSigned` is the actual hull log, and the certificate still has
`thetaSigned = 0`. -/
theorem arithmeticTupleSignedFloorCertificate_qSigned_eq_hullLog_of_unitRegion_measure_one
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1)
    (hlt : arithmeticTupleCanonicalHullHaarLog places tuple μ < -1) :
    (arithmeticTupleSignedFloorCertificate places tuple label μ).qSigned =
        arithmeticTupleCanonicalHullHaarLog places tuple μ ∧
      (arithmeticTupleSignedFloorCertificate places tuple label μ).thetaSigned = 0 :=
  ⟨arithmeticTupleSignedFloorCertificate_qSigned_eq_hullLog_of_hullLog_lt_neg_one
      places tuple label μ hlt,
    arithmeticTupleSignedFloorCertificate_thetaSigned_eq_zero_of_measure_one
      places tuple label μ hunit⟩

/-- Link evidence with the unit-region signed log as target. -/
def arithmeticTupleSignedFloorLinkEvidence
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    SignedFiniteStepXILinkEvidence
      (arithmeticTupleSignedFloorCertificate places tuple label μ) where
  targetSigned := arithmeticTupleIQHullUnitRegionHaarLog places tuple μ
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := by
    rw [arithmeticTupleSignedFloorCertificate_qSigned]
    exact le_trans (arithmeticTupleSignedFloorQ_le_hullLog places tuple μ)
      (arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog places tuple μ)
  target_le_theta := by
    rw [arithmeticTupleSignedFloorCertificate_thetaSigned]

/-- Corollary 3.12 conclusion from the non-vacuous signed certificate.  The
conclusion `qSigned <= thetaSigned` is the real log-volume comparison, not the
sign-blind `ofReal` conclusion. -/
theorem arithmeticTupleSignedFloorCor312Conclusion
    (label : Type uL) [Fintype label] [Nonempty label]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((arithmeticTupleSignedFloorCertificate places tuple label μ).toContract
        (arithmeticTupleSignedFloorLinkEvidence places tuple label μ
          ipl she apt hipl hshe hapt)) :=
  cor312_of_signed_finite_certificate
    (arithmeticTupleSignedFloorCertificate places tuple label μ)
    (arithmeticTupleSignedFloorLinkEvidence places tuple label μ
      ipl she apt hipl hshe hapt)

/-!
## Boundary

This file constructs a non-vacuous signed certificate for the actual arithmetic
tuple hull.  It is not the source `1, circ U` construction, it does not claim
source N5, and it does not prove the genuine source q comparison.  The floor
`-1` is an explicit mathematical choice that guarantees `q_negative`; in the
strict regime `hull log < -1` the certificate's `q` is the actual hull log.
-/

end

end LeanFormal.IUT.NumberFieldFinitePlace
