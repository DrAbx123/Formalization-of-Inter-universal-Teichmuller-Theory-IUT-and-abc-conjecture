import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-!
# S3140: the normalized 2l-th root residual for the explicit numeric Q_C formula

**Component, not paper object.**  Mainline task-48/49 reduced the S778 explicit
numeric q readout gap to ONE exact missing actual object: for every bad place b,
an actual CHOSEN 2l-th root generator in the NORMALIZED (Q_p-spectral) completion
at coefficient `rootHalfCoefficient = c_norm/(2l)`, i.e.

  `Nonempty (ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b)
      qVFamTensorTuple (rootHalfCoefficient T b))`.

The tree's TwoLthRootKumaActual gives the 2l-th root only in the DEFAULT
residue-norm completion (coefficient order/(2l)); the normalized/spectral
passage is the same e-normalization as R1 M2 / R2.  Once the supply below exists,
the per-b S778 formula `qPilotPaperLog_b = -(sum_i rootHalfCoefficient_{b,i}) *
log p_b` is a theorem by the already-green
`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`, and the
regional canonical Q_C numeric equality follows by the weighted sum.

Therefore the named residual for the explicit numeric statement remains
`S3134CanonicalRootedQFormulaGap` (shehdd S3134MainlineRootedHFaActual); this
file records its reduced supply shape so owners/consumers share one definition.
NO numeric equality `Q_C = -|log q|` is claimed.

Pages: IUT I Example 3.2(iv); IUT II Introduction pp.2-3; IUT III Definition
3.8(i) p.112; Remark 3.1.1(ii) (corpus 5408-5465); IUT IV Proposition 1.4(i).
Owner: mainline (supply) with shehdd consumer.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual

namespace LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The reduced exact missing supply for the explicit numeric Q_C formula: at
every bad place an actual chosen normalized 2l-th root generator. -/
def S3140NormalizedTwoLthRootSupply : Prop :=
  forall b : Bad (nativePlaceSelection T),
    Nonempty (ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (rootHalfCoefficient (l := l) T b))

/-- The supply is exactly the per-b normalized root existence. -/
theorem S3140NormalizedTwoLthRootSupply_iff :
    S3140NormalizedTwoLthRootSupply (l := l) T ↔
      (forall b : Bad (nativePlaceSelection T),
        Nonempty (ArithmeticTuplePureFractionalScalingData
          (qVFamTensorPlaces T b) qVFamTensorTuple
          (rootHalfCoefficient (l := l) T b))) :=
  Iff.rfl

/-- The named residual is still the S778 formula gap (shehdd's definition); the
supply above is its reduced exact-missing shape.  No numeric equality claimed. -/
def S3140CanonicalQFormulaGapAlias : Prop :=
  S3134CanonicalRootedQFormulaGap (l := l) T mu

#check S3140NormalizedTwoLthRootSupply
#check S3140NormalizedTwoLthRootSupply_iff
#check S3140CanonicalQFormulaGapAlias

end LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual
