import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientInclusionActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-!
# Root-normalized Theta hull

For each bad place b, the paper theta value is built from the 2l-th root of
the classical qVFamily q:

  qVFamPaperRootCoefficient b = order(qVFamily T b) / (2l),

and the theta tensor coefficient is j^2 times this root coefficient.  The old
order coefficient is exactly 2l times the root coefficient.

This file constructs, per b:

* the actual root theta values from hodgeTwoLthRoot;
* the actual root fractional-lattice scaled regions;
* the actual root image set and its closure hull;
* the old order regions/hull for comparison;
* the actual coefficient-level root hull log formula.

It proves the exact 1/(2l) relation globally: the old order hull log is 2l times
the root hull log, with the factor applied once, not once per bad place.

The actual Haar/normalized-log identification of the root hull region is
recorded as an exact gap; it is not replaced by the coefficient formula.
No inequality, no old global equality, no LGP/Kummer/Ind.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootNormalizedThetaHullActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual root theta value at a signed label, from the actual 2l-th root. -/
noncomputable def rootThetaValue (j : SignedLabel l.value) :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  qVFamilyPaperThetaValueRoot T b j

/-- The root theta value is the j^2 power of hodgeTwoLthRoot. -/
theorem rootThetaValue_eq (j : SignedLabel l.value) :
    rootThetaValue T b j = (hodgeTwoLthRoot T b) ^ (gaussExponent j.1).toNat :=
  rfl

/-- The actual root coefficient as a tensor coefficient function. -/
noncomputable def rootThetaCoefficient (j : SignedLabel l.value) :
    qVFamTensorV → Real :=
  fun _ => qVFamPaperThetaTensorCoefficient T b j

/-- The actual root fractional-lattice scaled region. -/
noncomputable def rootThetaRegion (j : SignedLabel l.value) :
    Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (rootThetaCoefficient T b j)

/-- The actual finite root image-region set over the signed labels. -/
noncomputable def rootThetaImageSet : Set (qVFamTensorBlock T b) :=
  ⋃ j : SignedLabel l.value, rootThetaRegion T b j

/-- The actual root hull: the closure of the root image-region set. -/
noncomputable def rootThetaHull : Set (qVFamTensorBlock T b) :=
  closure (rootThetaImageSet T b)

/-- The old order fractional-lattice scaled region. -/
noncomputable def orderThetaRegion (j : SignedLabel l.value) :
    Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (qVFamThetaTensorCoefficient T b j)

/-- The old order image-region set. -/
noncomputable def orderThetaImageSet : Set (qVFamTensorBlock T b) :=
  ⋃ j : SignedLabel l.value, orderThetaRegion T b j

/-- The old order hull. -/
noncomputable def orderThetaHull : Set (qVFamTensorBlock T b) :=
  closure (orderThetaImageSet T b)

/-- The actual root coefficient is 2l times smaller than the old order
coefficient, coordinatewise. -/
theorem orderThetaCoefficient_eq_twoL_mul_root
    (j : SignedLabel l.value) :
    qVFamThetaTensorCoefficient T b j =
      fun _ : qVFamTensorV =>
        (2 * l.value : Real) * rootThetaCoefficient T b j () := by
  funext i
  simp only [rootThetaCoefficient]
  rw [qVFamThetaTensorCoefficient_eq_twoL_mul_rootCoefficient]
  rfl

/-- The total old order coefficient is 2l times the total root coefficient at
the minimal signed label. -/
theorem orderTotalCoefficient_eq_twoL_mul_rootTotal :
    (∑ _ : qVFamTensorV, qVFamThetaTensorCoefficient T b
        (oneSignedLabel (l := l))) =
      (2 * l.value : Real) *
        (∑ _ : qVFamTensorV, rootThetaCoefficient T b
          (oneSignedLabel (l := l)) ()) := by
  rw [Finset.sum_const, Finset.sum_const]
  simp only [rootThetaCoefficient, qVFamPaperThetaTensorCoefficient]
  rw [qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient]
  ring

/-- The actual root coefficient formula log. -/
noncomputable def rootThetaHullFormulaLog : Real :=
  - (∑ _ : qVFamTensorV, rootThetaCoefficient T b
      (oneSignedLabel (l := l)) ()) *
      Real.log (qVFamP T b : Real)

/-- The old order coefficient formula log. -/
noncomputable def orderThetaHullFormulaLog : Real :=
  - (∑ _ : qVFamTensorV, qVFamThetaTensorCoefficient T b
      (oneSignedLabel (l := l))) *
      Real.log (qVFamP T b : Real)

/-- The exact global 1/(2l) relation: the old order formula log is 2l times
the root formula log.  The factor appears once in the total coefficient, not
once per bad place. -/
theorem orderThetaHullFormulaLog_eq_twoL_mul_root :
    orderThetaHullFormulaLog T b =
      (2 * l.value : Real) * rootThetaHullFormulaLog T b := by
  unfold orderThetaHullFormulaLog rootThetaHullFormulaLog
  rw [orderTotalCoefficient_eq_twoL_mul_rootTotal]
  ring

/-- The root formula log is the old formula log divided by 2l. -/
theorem rootThetaHullFormulaLog_eq_div_twoL :
    rootThetaHullFormulaLog T b =
      orderThetaHullFormulaLog T b / (2 * l.value : Real) := by
  rw [orderThetaHullFormulaLog_eq_twoL_mul_root]
  field_simp [show (2 * l.value : Real) ≠ 0 by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero]

/-- The actual root hull normalized log-volume, defined from the actual
arithmetic tuple normalized log-volume on the root hull. -/
noncomputable def rootThetaHullNormalizedLog
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) (qVFamTensorTuple) mu
    (rootThetaHull T b)

/-- Exact gap data for the root hull normalized log: actual Haar positivity and
finiteness, the identification of the closure hull with the minimal root scaled
region, and the actual root ArithmeticTuplePureFractionalScalingData. -/
structure RootThetaHullNormalizationGap
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] : Prop where
  rootHullHaarPos : 0 < mu (rootThetaHull T b)
  rootHullHaarFinite : mu (rootThetaHull T b) < ⊤
  rootHull_eq_minimalRegion :
    rootThetaHull T b =
      thetaTensorScaledRegion
        (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
        (rootThetaCoefficient T b (oneSignedLabel (l := l)))
  scalingData : ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) (qVFamTensorTuple)
    (rootThetaCoefficient T b (oneSignedLabel (l := l)))

/-- Exact missing root normalization object. -/
def RootThetaHullNormalizationGapRequired
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] : Prop :=
  Nonempty (RootThetaHullNormalizationGap (l := l) T b mu)

/-- Conditional actual normalized-log equality from the exact root gap data. -/
theorem rootThetaHullNormalizedLog_eq_formula_of_gap
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu]
    (G : RootThetaHullNormalizationGap (l := l) T b mu) :
    rootThetaHullNormalizedLog (l := l) T b mu =
      rootThetaHullFormulaLog (l := l) T b := by
  unfold rootThetaHullNormalizedLog rootThetaHullFormulaLog
  rw [G.rootHull_eq_minimalRegion]
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu G.scalingData

end LeanFormal.IUT.XiFPaper.RootNormalizedThetaHullActualAdapted
end
