import tmp.sheaf.xif.paper.RootTensorThetaHullActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual

/-! # S255: blockHaar pushforward to L and actual Haar scalar -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S255CommonHaarOnLActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open MeasureTheory

noncomputable instance rootNormedHaarIsAddHaar :
    Measure.IsAddHaarMeasure
      (LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual.rootNormedHaar T b) := by
  unfold LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual.rootNormedHaar
  infer_instance

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Pushforward of the independent block Haar to L by the actual continuous
linear isometry. -/
noncomputable def commonHaarOnL : Measure (rootNormedExtension T b) :=
  (blockHaar T b).map (blockLinearIsometryEquiv T b).toContinuousLinearEquiv

/-- The pushforward is an additive Haar measure. -/
noncomputable instance commonHaarOnLIsAddHaar :
    Measure.IsAddHaarMeasure (commonHaarOnL T b) := by
  unfold commonHaarOnL
  exact ContinuousLinearEquiv.isAddHaarMeasure_map
    (blockLinearIsometryEquiv T b).toContinuousLinearEquiv (blockHaar T b)

/-- Actual Haar-uniqueness scalar between the pushed block Haar and
rootNormedHaar. -/
noncomputable def commonHaarScalarFactor
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : ENNReal :=
  Measure.addHaarScalarFactor (commonHaarOnL T b)
    (LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual.rootNormedHaar T b)

/-- Haar uniqueness: on open sets, the pushed block Haar is the scalar times
rootNormedHaar. -/
theorem commonHaarOnL_eq_smul_open {s : Set (rootNormedExtension T b)}
    (hs : IsOpen s) :
    commonHaarOnL (T := T) b s =
      commonHaarScalarFactor T b • rootNormedHaar T b s :=
  Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen
    (commonHaarOnL T b)
    (LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual.rootNormedHaar T b) hs

/-- Actual common-Haar scalar object. -/
structure CommonHaarScalarObject where
  commonHaar : Measure (rootNormedExtension T b)
  commonHaar_eq : commonHaar = commonHaarOnL (T := T) b
  rootNormedHaar : Measure (rootNormedExtension T b)
  rootNormedHaar_eq : rootNormedHaar = LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual.rootNormedHaar T b
  scalar : ENNReal
  scalar_eq : scalar = commonHaarScalarFactor T b

noncomputable def commonHaarScalarObject :
    CommonHaarScalarObject (T := T) b where
  commonHaar := commonHaarOnL (T := T) b
  commonHaar_eq := rfl
  rootNormedHaar := LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual.rootNormedHaar T b
  rootNormedHaar_eq := rfl
  scalar := commonHaarScalarFactor T b
  scalar_eq := rfl

end LeanFormal.IUT.XiFPaper.S255CommonHaarOnLActual

end
