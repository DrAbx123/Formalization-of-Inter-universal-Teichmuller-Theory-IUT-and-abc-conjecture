import tmp.sheaf.xif.paper.S3131HullActualReadout
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-! # S3131: the exact coefficient/containment gap of Batch A

Batch A needs the actual q-pilot region to be contained in the actual Theta
hull on the same fixed input C.  The tree carries TWO paper root-coefficient
conventions, and the containment between them is the exact remaining
normalization comparison:

* normalized-spectral convention (QVFamNormalizedGeneratorSupplyActual:54-149):
    c_norm b = -logb_p ||qVFamily q||_spectral,  positive actual coefficient;
  its rooted form is rootHalfCoefficient b = c_norm b/(2l)
  (RootNormalizedContainmentActual:56-58), the S778 qPilotPaperRegion;
  the S3131 q-side region qPilotNormRegion is the unrooted c_norm region;
* default-residue convention (BadPlacePaperRootThetaHullActual:35-38):
    paperRootCoefficient b = order(qVFamily b)/(2l)
  (qVFamPaperRootCoefficient), used by the paper Theta hull
  paperRootThetaHullNonzero (S779) and by S805 qPilotPaperRegion.

The missing source data is the comparison of the two normalizations on the
same actual qVFamily element, here recorded as

  S3131CoefficientComparisonRequired b :
    forall i, paperRootCoefficient b <= c_norm b        (order/(2l) <= c_norm),
  S3131RootedCoefficientComparisonRequired b :
    forall i, paperRootCoefficient b <= rootHalfCoefficient b  (order <= c_norm).

Neither is asserted.  The rooted one implies the unrooted one.  Either one
gives S3131QRegionContainedInHull b (qPilotNormRegion subset paperRootThetaHullNonzero)
by the actual fractional-lattice coefficient monotonicity and the actual
S805/S779 hull containment.  So S3131QRegionContainedInHull is discharged
from a comparison of two actual real coefficients, not assumed.

No sorry/axiom/True/PUnit.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131CoefficientGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S3131HullActualReadout
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The normalized-spectral qVFamily coefficient family at b (c_norm). -/
noncomputable def S3131QRegionCoefficient : qVFamTensorV → Real :=
  rootNormCoefficient (l := l) T b

/-- The rooted normalized-spectral coefficient family at b: c_norm/(2l). -/
noncomputable def S3131RootedQRegionCoefficient : qVFamTensorV → Real :=
  rootHalfCoefficient (l := l) T b

/-- The paper default-residue coefficient family at b: order/(2l). -/
noncomputable def S3131PaperQRegionCoefficient : qVFamTensorV → Real :=
  paperRootCoefficientFamily (l := l) T b

/-- **Exact missing normalization comparison (unrooted form):** the paper
default-residue coefficient order/(2l) is at most the normalized-spectral
qVFamily coefficient c_norm.  This is exactly the comparison of the two actual
completion normalizations on the same qVFamily element.  Not asserted. -/
def S3131CoefficientComparisonRequired : Prop :=
  ∀ i : qVFamTensorV,
    S3131PaperQRegionCoefficient (l := l) T b i ≤
      S3131QRegionCoefficient (l := l) T b i

/-- **Exact missing normalization comparison (rooted form):** order/(2l) is at
most c_norm/(2l), equivalently order <= c_norm.  This is the comparison of the
two tree conventions S805/S779 paperRootCoefficient and S778/S3131
rootHalfCoefficient.  Not asserted. -/
def S3131RootedCoefficientComparisonRequired : Prop :=
  ∀ i : qVFamTensorV,
    S3131PaperQRegionCoefficient (l := l) T b i ≤
      S3131RootedQRegionCoefficient (l := l) T b i

/-- Unrooted form in terms of the actual registered coefficients. -/
theorem S3131CoefficientComparisonRequired_iff :
    S3131CoefficientComparisonRequired (l := l) T b ↔
      qVFamPaperRootCoefficient (l := l) T b ≤ qVFamNormalizedCoefficient T b := by
  constructor
  · intro h
    simpa [S3131PaperQRegionCoefficient, S3131QRegionCoefficient,
      paperRootCoefficientFamily, rootNormCoefficient,
      qVFamNormalizedCoefficientFamily] using h ()
  · intro h i
    simpa [S3131PaperQRegionCoefficient, S3131QRegionCoefficient,
      paperRootCoefficientFamily, rootNormCoefficient,
      qVFamNormalizedCoefficientFamily] using h

/-- Rooted form in terms of rootHalfCoefficient and paperRootCoefficient. -/
theorem S3131RootedCoefficientComparisonRequired_iff :
    S3131RootedCoefficientComparisonRequired (l := l) T b ↔
      qVFamPaperRootCoefficient (l := l) T b ≤ rootHalfCoefficient (l := l) T b () := by
  constructor
  · intro h
    simpa [S3131PaperQRegionCoefficient, S3131RootedQRegionCoefficient,
      paperRootCoefficientFamily, rootHalfCoefficient, rootNormCoefficient,
      qVFamNormalizedCoefficientFamily] using h ()
  · intro h i
    simpa [S3131PaperQRegionCoefficient, S3131RootedQRegionCoefficient,
      paperRootCoefficientFamily, rootHalfCoefficient, rootNormCoefficient,
      qVFamNormalizedCoefficientFamily] using h

/-- The rooted comparison implies the unrooted comparison: multiplying
order <= c_norm by the positive factor 1/(2l) gives order/(2l) <= c_norm/(2l). -/
theorem S3131RootedCoefficientComparison_implies_unrooted
    (h : S3131RootedCoefficientComparisonRequired (l := l) T b) :
    S3131CoefficientComparisonRequired (l := l) T b := by
  intro i
  have hri : S3131PaperQRegionCoefficient (l := l) T b i ≤
      S3131RootedQRegionCoefficient (l := l) T b i := h i
  have hhalf : S3131RootedQRegionCoefficient (l := l) T b i =
      S3131QRegionCoefficient (l := l) T b i / (2 * (l.value : Real)) := rfl
  have h1 : (1 : Real) ≤ 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    linarith
  have hc : 0 ≤ S3131QRegionCoefficient (l := l) T b i := by
    unfold S3131QRegionCoefficient rootNormCoefficient qVFamNormalizedCoefficientFamily
    exact qVFamNormalizedCoefficient_nonneg T b
  calc S3131PaperQRegionCoefficient (l := l) T b i
      ≤ S3131RootedQRegionCoefficient (l := l) T b i := hri
    _ = S3131QRegionCoefficient (l := l) T b i / (2 * (l.value : Real)) := hhalf
    _ ≤ S3131QRegionCoefficient (l := l) T b i := div_le_self hc h1

/-- **Containment of the q-pilot region in the paper q-pilot region of S805
from the exact coefficient comparison.** -/
theorem S3131QRegion_subset_paperQRegion
    (h : S3131CoefficientComparisonRequired (l := l) T b) :
    (qPilotNormRegion (l := l) T b : Set (qVFamTensorBlock T b)) ⊆
      (qPilotPaperRegion (l := l) T b : Set (qVFamTensorBlock T b)) := by
  intro x hx
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (rootNormCoefficient (l := l) T b) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    exact h i
  exact (mul_le_mul' hlat le_rfl) hx

/-- **The exact named containment gap is discharged from the exact coefficient
comparison.**  qPilotNormRegion is contained in the actual paper Theta hull
paperRootThetaHullNonzero because the comparison puts it in the S805 paper
q-pilot region, which the actual OR-expansion containment puts in the hull. -/
theorem S3131QRegionContainedInHull_of_coefficient
    (h : S3131CoefficientComparisonRequired (l := l) T b) :
    S3131QRegionContainedInHull (l := l) T b := by
  intro x hx
  have hx' : x ∈ qPilotPaperRegion (l := l) T b :=
    S3131QRegion_subset_paperQRegion (l := l) T b h hx
  exact qPilotPaperRegion_subset_nonzeroHull (l := l) T b hx'

#check S3131CoefficientComparisonRequired_iff
#check S3131RootedCoefficientComparison_implies_unrooted
#check S3131QRegionContainedInHull_of_coefficient

end LeanFormal.IUT.XiFPaper.S3131CoefficientGapActual

end
