import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-! # Normalized root coefficient and root hull containment

The root coefficient is c_norm/(2l), where c_norm is the actual normalized
qVFamily coefficient qVFamPureCoefficient.  The qPilot classical region is
F(c_norm) O_hol; the root theta regions use j^2 c_root with
c_root = c_norm/(2l).  Since c_root <= c_norm (for c_norm >= 0), the qPilot
region is contained in the root theta closure hull, and normalized-log
monotonicity gives qPilotLog <= rootThetaHullLog.

The actual normalized scaling data comes from a NormalizedGeneratorSupply via
qVFamPureFractionalScalingData_of_supply.  No default coefficient is used.

No root hull equality is asserted.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual normalized qVFamily coefficient c_norm. -/
noncomputable def rootNormCoefficient : qVFamTensorV -> Real :=
  qVFamNormalizedCoefficientFamily (l := l) T b

/-- Paper root coefficient c_root = c_norm/(2l). -/
noncomputable def rootHalfCoefficient : qVFamTensorV -> Real :=
  fun i => rootNormCoefficient (l := l) T b i / (2 * (l.value : Real))

theorem rootHalfCoefficient_le_norm :
    ∀ i, rootHalfCoefficient (l := l) T b i <= rootNormCoefficient (l := l) T b i := by
  intro i
  have hc : 0 <= rootNormCoefficient (l := l) T b i := by
    unfold rootNormCoefficient
    exact qVFamNormalizedCoefficient_nonneg (l := l) T b
  unfold rootHalfCoefficient
  have hden : (1 : Real) <= 2 * (l.value : Real) := by
    have : (5 : Real) <= l.value := by exact_mod_cast l.ge_five
    nlinarith
  have hdenpos : 0 < 2 * (l.value : Real) := by positivity
  calc
    rootNormCoefficient (l := l) T b i / (2 * (l.value : Real)) <=
        rootNormCoefficient (l := l) T b i / 1 := by
      apply div_le_div_of_nonneg_left hc (by norm_num) hden
    _ = rootNormCoefficient (l := l) T b i := by ring

variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- The qPilot classical region with the normalized coefficient. -/
abbrev qPilotNormRegion : Set (qVFamTensorBlock T b) :=
  qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootNormCoefficient (l := l) T b)

/-- The root hull with coefficient c_root = c_norm/(2l). -/
abbrev rootNormHull : Set (qVFamTensorBlock T b) :=
  rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootHalfCoefficient (l := l) T b)

/-- Actual scaling data from a normalized generator supply. -/
noncomputable def rootNormScalingData :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (rootNormCoefficient (l := l) T b) :=
  qVFamNormalizedPureFractionalScalingData (l := l) T b

/-- Containment of the normalized qPilot region in the root hull. -/
theorem qPilotNormRegion_subset_rootNormHull :
    qPilotNormRegion (l := l) T b ⊆ rootNormHull (l := l) T b :=
  qPilotClassicalRegion_subset_rootHull
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootNormCoefficient (l := l) T b)
    (rootHalfCoefficient (l := l) T b)
    (rootHalfCoefficient_le_norm (l := l) T b)
    (oneLabel l) (gaussExponent_oneLabel l)

/-- qPilot normalized log formula from normalized scaling data. -/
theorem qPilotNormLog_eq :
    qPilotClassicalLog
      (qVFamTensorPlaces T b) qVFamTensorTuple mu
      (rootNormCoefficient (l := l) T b)
      (rootNormScalingData (l := l) T b) =
      -((∑ i, rootNormCoefficient (l := l) T b i) *
        Real.log (qVFamTensorP T b : Real)) :=
  qPilotClassicalLog_eq
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootNormCoefficient (l := l) T b)
    (rootNormScalingData (l := l) T b)

/-- Scalar inequality qPilotSigned <= rootThetaHullLog. -/
theorem qPilotNormLog_le_rootNormHullLog
    (hpos : 0 < mu (qPilotNormRegion (l := l) T b))
    (hfin : mu (rootNormHull (l := l) T b) < ⊤) :
    qPilotClassicalLog
        (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootNormCoefficient (l := l) T b)
        (rootNormScalingData (l := l) T b) <=
      rootThetaHullLog
        (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootHalfCoefficient (l := l) T b) :=
  qPilotClassicalLog_le_rootThetaHullLog
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootNormCoefficient (l := l) T b)
    (rootHalfCoefficient (l := l) T b)
    (rootNormScalingData (l := l) T b)
    (rootHalfCoefficient_le_norm (l := l) T b)
    (oneLabel l) (gaussExponent_oneLabel l) hpos hfin

end LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual

end
