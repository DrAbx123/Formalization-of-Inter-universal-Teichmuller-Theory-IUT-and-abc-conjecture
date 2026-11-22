import tmp.sheaf.xif.paper.Node09P5HullInequalityFinalActual
import tmp.sheaf.xif.paper.Node09P5ThetaSideFinalActual
import tmp.sheaf.xif.paper.Node09P5NormalizedRegionActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

namespace LeanFormal.IUT.XiFPaper.Node09P5ThetaReadingZeroActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
variable [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]
variable [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The qVFam theta hull equals the holomorphic unit region: both inclusions are
actual (regions have nonnegative coefficients, and label 0 is a theta label). -/
theorem qVFamLocalThetaHull_eq_holomorphic :
    qVFamLocalThetaHull T b =
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
  apply Set.Subset.antisymm
  · exact qVFamLocalThetaHull_subset_holomorphic (l := l) T b
  · exact qVFamHolomorphicLattice_subset_thetaHull (l := l) T b

/-- The per-b qVFam theta-hull normalized log-volume is zero. -/
theorem qVFamLocalThetaHullLogVolume_eq_zero :
    qVFamLocalThetaHullLogVolume T b = 0 := by
  unfold qVFamLocalThetaHullLogVolume
  rw [qVFamLocalThetaHull_eq_holomorphic (l := l) T b]
  exact qVFamUnitRegionVolume_eq_zero T b

/-- The theta-side reading is zero: the hull collapses to the unit region. -/
theorem qVFamThetaReading_eq_zero
    (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l)
    [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      BorelSpace (qVFamTensorBlock X.S b)] :
    qVFamThetaReading X = 0 := by
  unfold qVFamThetaReading
  apply Finset.sum_eq_zero
  intro b _
  exact qVFamLocalThetaHullLogVolume_eq_zero X.S b

/-- Therefore the theta reading cannot be a positive Thm 1.10 logQ value. -/
theorem qVFamThetaReading_ne_pos_logQ
    (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l)
    [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      BorelSpace (qVFamTensorBlock X.S b)]
    {logQ : Real} (hlogQ : 0 < logQ) :
    qVFamThetaReading X ≠ logQ := by
  rw [qVFamThetaReading_eq_zero X]
  exact ne_of_lt hlogQ

#print axioms qVFamLocalThetaHull_eq_holomorphic
#print axioms qVFamThetaReading_eq_zero

end LeanFormal.IUT.XiFPaper.Node09P5ThetaReadingZeroActual
end