import tmp.sheaf.xif.paper.RootHullMeasureActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
open CategoryTheory
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The actual interface on one native bad-place tensor block, with the
canonical unit reference as unit region and the actual normalized root hull. -/
noncomputable def S2586IQHullLogVolumeInterface :
    IQHullLogVolumeInterface (qVFamTensorBlock T b) where
  imageSet := rootThetaImageSet (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootHalfCoefficient (l := l) T b)
  hull := rootNormHull (l := l) T b
  imageSet_subset_hull := by
    intro x hx
    exact subset_closure hx
  logVolume := fun S => (Measure.addHaar : Measure (qVFamTensorBlock T b)) S
  logVolume_mono := by
    intro S U hSU
    exact measure_mono hSU
  unitRegion := arithmeticTupleCanonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, rootNormHull_subset_holomorphic (l := l) T b hx, rfl⟩
  unitRegion_logVolume_lt_top := by
    exact (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.measure_lt_top
  scaleShift_unitRegion_logVolume_le := by
    rw [show id '' arithmeticTupleCanonicalUnitReference
        (qVFamTensorPlaces T b) qVFamTensorTuple =
        arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple by
      ext x
      simp]

#check S2586IQHullLogVolumeInterface
#print axioms S2586IQHullLogVolumeInterface

end LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
end
