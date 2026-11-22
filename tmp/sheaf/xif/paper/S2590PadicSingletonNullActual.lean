import tmp.sheaf.xif.paper.S2589DictionaryMinimalActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import Mathlib.MeasureTheory.Group.Measure
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorNontrivial

noncomputable section
open MeasureTheory
open scoped Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

theorem S2590SingletonNull :
    S2589SingletonNull (S2586IQHullLogVolumeInterface T b) := by
  haveI : Module.IsTorsionFree ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) :=
    (Module.finBasis ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)).isTorsionFree
  haveI : Filter.NeBot (nhdsWithin (0 : qVFamTensorBlock T b) {(0 : qVFamTensorBlock T b)}ᶜ) :=
    Module.punctured_nhds_neBot ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) 0
  haveI : NullSingletonClass
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) :=
    MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass _
  intro x
  exact MeasureTheory.NullSingletonClass.measure_singleton x

#check S2590SingletonNull
#print axioms S2590SingletonNull

end LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
end