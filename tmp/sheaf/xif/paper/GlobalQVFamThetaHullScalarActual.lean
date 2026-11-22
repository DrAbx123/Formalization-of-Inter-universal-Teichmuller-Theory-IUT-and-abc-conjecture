import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-!
# Global qVFamily theta hull scalar

Bad places carry different rational primes, so there is no single fixed-p tensor
block.  For each b : Bad we use the actual per-b dependency tensor block from
QVFamTensorCoefficientActual:

* qVFamTensorBlock T b;
* the actual theta scaled regions qVFamThetaTensorRegion T b j;
* the actual local theta hull, the closure of their union in that block;
* the actual q-pilot local region with coefficient qVFamTensorCoefficient.

The local q-pilot region is one of the theta regions (label 1, gauss exponent 1),
so qPilot local ⊆ theta hull local.  arithmeticTupleNormalizedLogVolume_mono
then gives the local log inequality under the actual positive/finite measure
conditions, and the global scalar is the weighted sum over b.

No single fixed-p block, no fake PUnit carrier, no inequality assumed.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]

/-- The signed label 1, with gauss exponent one. -/
noncomputable def oneSignedLabel : SignedLabel l.value :=
  ⟨1, by
    have h5 : 5 ≤ l.value := l.ge_five
    have hge : 1 ≤ lStar l.value := by
      unfold lStar
      omega
    rw [Set.mem_Icc]
    constructor
    · omega
    · exact_mod_cast hge⟩

/-- The gauss exponent of label 1 is one. -/
theorem oneSignedLabel_gauss :
    (gaussExponent (oneSignedLabel (l := l)).1).toNat = 1 := by
  unfold oneSignedLabel gaussExponent
  norm_num

/-- Actual q-pilot local region at b: the scaled region with qVFamily order. -/
noncomputable def qVFamLocalQPilotRegion :
    Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (fun _ => qVFamTensorCoefficient T b)

/-- Actual local theta hull: closure of the union of the actual theta regions. -/
noncomputable def qVFamLocalThetaHull :
    Set (qVFamTensorBlock T b) :=
  closure (⋃ j : SignedLabel l.value, qVFamThetaTensorRegion T b j)

/-- The q-pilot local region is contained in the local theta hull: label 1 has
theta coefficient exactly the qVFamily order. -/
theorem qVFamLocalQPilotRegion_subset_thetaHull :
    qVFamLocalQPilotRegion T b ⊆ qVFamLocalThetaHull T b := by
  intro x hx
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨oneSignedLabel (l := l), ?_⟩
  have hcoef : qVFamThetaTensorCoefficient T b (oneSignedLabel (l := l)) =
      fun _ => qVFamTensorCoefficient T b := by
    funext i
    unfold qVFamThetaTensorCoefficient
    rw [oneSignedLabel_gauss]
    ring
  have hx' : x ∈ thetaTensorScaledRegion
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
      (qVFamThetaTensorCoefficient T b (oneSignedLabel (l := l))) := by
    rw [hcoef]
    exact hx
  exact hx'

/-- Actual local q-pilot normalized log-volume. -/
noncomputable def qVFamLocalQPilotLogVolume
    (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (qVFamLocalQPilotRegion T b)

/-- Actual local theta hull normalized log-volume. -/
noncomputable def qVFamLocalThetaHullLogVolume
    (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (qVFamLocalThetaHull T b)

/-- Local log inequality from normalizedLogVolume_mono, under the actual
positive/finite measure conditions of the q-pilot region and hull. -/
theorem qVFamLocalQPilotLogVolume_le_thetaHull
    (hpos : 0 < Measure.addHaar (qVFamLocalQPilotRegion T b))
    (hfin : Measure.addHaar (qVFamLocalThetaHull T b) < ⊤) :
    qVFamLocalQPilotLogVolume T b ≤ qVFamLocalThetaHullLogVolume T b :=
  arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (qVFamLocalQPilotRegion_subset_thetaHull (l := l) T b) hpos hfin

/-- Actual local weight is nonnegative. -/
theorem nativeBadLocalWeight_nonneg
    (b : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b := by
  unfold nativeBadLocalWeight localNormalizedWeight
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Global qVFamily q-pilot scalar: weighted sum of local normalized volumes. -/
noncomputable def globalQVFamQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qVFamLocalQPilotLogVolume T b

/-- Global theta hull scalar: weighted sum of local theta hull log-volumes. -/
noncomputable def globalQVFamThetaHullLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qVFamLocalThetaHullLogVolume T b

/-- Global local-to-global inequality from the per-b local inequalities. -/
theorem globalQVFamQPilotLog_le_thetaHull
    (h : ∀ b : Bad (nativePlaceSelection T),
      qVFamLocalQPilotLogVolume T b ≤ qVFamLocalThetaHullLogVolume T b) :
    globalQVFamQPilotLog T ≤ globalQVFamThetaHullLog T := by
  unfold globalQVFamQPilotLog globalQVFamThetaHullLog
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (h b) (nativeBadLocalWeight_nonneg T b)

/-- Actual global scalar data. -/
structure GlobalQVFamThetaHullScalarData where
  localQPilotLog : Bad (nativePlaceSelection T) → Real
  localQPilotLog_eq : localQPilotLog =
    qVFamLocalQPilotLogVolume T
  localThetaHullLog : Bad (nativePlaceSelection T) → Real
  localThetaHullLog_eq : localThetaHullLog =
    qVFamLocalThetaHullLogVolume T
  globalQPilotLog : Real
  globalQPilotLog_eq : globalQPilotLog = globalQVFamQPilotLog T
  globalThetaHullLog : Real
  globalThetaHullLog_eq : globalThetaHullLog = globalQVFamThetaHullLog T

/-- The actual global scalar data constructor. -/
noncomputable def globalQVFamThetaHullScalarData :
    GlobalQVFamThetaHullScalarData T where
  localQPilotLog := qVFamLocalQPilotLogVolume T
  localQPilotLog_eq := rfl
  localThetaHullLog := qVFamLocalThetaHullLogVolume T
  localThetaHullLog_eq := rfl
  globalQPilotLog := globalQVFamQPilotLog T
  globalQPilotLog_eq := rfl
  globalThetaHullLog := globalQVFamThetaHullLog T
  globalThetaHullLog_eq := rfl

end LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual

end
