import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Local per-b Theta tensor hull log-volume

For each actual bad place b, this file uses

* the actual one-factor tensor block qVFamTensorBlock at the F-place over b;
* the actual qVFamily theta tensor region qVFamThetaTensorRegion j b;
* the actual finite union over the theta labels, and its actual topological
  closure/hull thetaTensorHull;
* the actual normalized Haar log-volume arithmeticTupleNormalizedLogVolume.

The result is a per-b local hull scalar. No sum over b and no cross-b
identification is formed. No inequality is asserted.

No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.LocalBThetaHullLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily theta coefficient family at b. -/
noncomputable def localThetaCoefficientFamily :
    SignedLabel l.value → qVFamTensorV → Real :=
  fun j => qVFamThetaTensorCoefficient T b j

/-- The actual qVFamily theta image union at b. -/
noncomputable def localThetaImageSet :
    Set (qVFamTensorBlock T b) :=
  thetaTensorImageSet
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (localThetaCoefficientFamily T b)

/-- The actual per-b hull: the topological closure of the theta image union. -/
noncomputable def localThetaHull :
    Set (qVFamTensorBlock T b) :=
  thetaTensorHull
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (localThetaCoefficientFamily T b)

/-- The actual per-b hull is the closure of the actual image union. -/
theorem localThetaHull_eq_closure :
    localThetaHull T b =
      closure (localThetaImageSet T b) :=
  rfl

/-- The actual per-b image union is the union of the qVFamily theta tensor
regions. -/
theorem localThetaImageSet_eq_iUnion :
    localThetaImageSet T b =
      ⋃ j : SignedLabel l.value, qVFamThetaTensorRegion T b j :=
  rfl

/-- The actual per-b additive Haar measure on the one-factor tensor block. -/
noncomputable def localThetaHullHaar
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] :
    Measure (qVFamTensorBlock T b) :=
  Measure.addHaar

/-- The actual per-b hull log-volume, using the degree-normalized Haar
log-volume arithmeticTupleNormalizedLogVolume. -/
noncomputable def localThetaHullLogVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple mu (localThetaHull T b)

/-- The per-b hull log-volume with the actual additive Haar measure. -/
noncomputable def localThetaHullLogVolumeAddHaar
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] : Real :=
  localThetaHullLogVolume T b (localThetaHullHaar T b)

/-- The actual per-b hull log-volume is exactly the normalized log-volume of
the closure hull. -/
theorem localThetaHullLogVolume_eq
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) :
    localThetaHullLogVolume T b mu =
      arithmeticTupleNormalizedLogVolume
        (qVFamTensorPlaces T b) qVFamTensorTuple mu (localThetaHull T b) :=
  rfl

/-- The actual additive-Haar version is the normalized log-volume of the hull
at the actual Haar measure. -/
theorem localThetaHullLogVolumeAddHaar_eq
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] :
    localThetaHullLogVolumeAddHaar T b =
      arithmeticTupleNormalizedLogVolume
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (localThetaHullHaar T b) (localThetaHull T b) :=
  rfl

/-- Actual local per-b hull data. No cross-b merger is included. -/
structure LocalBThetaHullLogVolumeData where
  bad : Bad (nativePlaceSelection T)
  hull : Set (qVFamTensorBlock T bad)
  hull_eq : hull = localThetaHull T bad
  haar : Measure (qVFamTensorBlock T bad)
  haar_eq : haar = localThetaHullHaar T bad
  logVolume : Real
  logVolume_eq : logVolume = localThetaHullLogVolume T bad haar

/-- The actual local per-b hull data at b. -/
noncomputable def localBThetaHullLogVolumeData
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] :
    LocalBThetaHullLogVolumeData (l := l) T b where
  bad := b
  hull := localThetaHull T b
  hull_eq := rfl
  haar := localThetaHullHaar T b
  haar_eq := rfl
  logVolume := localThetaHullLogVolume T b (localThetaHullHaar T b)
  logVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.LocalBThetaHullLogVolumeActual

end
