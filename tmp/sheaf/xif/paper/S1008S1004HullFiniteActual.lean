import tmp.sheaf.xif.paper.S1004QVFamFiniteLinearizationActual
import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic

-- S1008: s1004Hull is the linear image of paperRootThetaImageNZ, which
-- lies in the compact canonical unit reference O.  Hence s1004Hull is
-- compact and has finite Haar measure.

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1008S1004HullFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Image of paperRootThetaImageNZ under the finite linearization. -/
theorem s1008Hull_subset_image_O :
    s1004Hull (l := l) T b ⊆
      s1004E (l := l) T b '' S922O (l := l) T b :=
  Set.image_mono (paperRootThetaImageNZ_subset_O (l := l) T b)

theorem s1008O_compact : IsCompact (S922O (l := l) T b) :=
  (isCompact_arithmeticTupleCanonicalRegions
    (qVFamTensorPlaces T b) qVFamTensorTuple).2

theorem s1008E_continuous :
    Continuous (s1004E (l := l) T b) :=
  LinearMap.continuous_of_finiteDimensional
    (s1004E (l := l) T b : qVFamTensorBlock T b →ₗ[ℚ_[qVFamTensorP T b]]
      FiniteLogShellCarrier (qVFamTensorP T b)
        (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)))

theorem s1008Hull_measure_lt_top :
    (s1004H (l := l) T b).measure (s1004Hull (l := l) T b) < ⊤ := by
  letI : Measure.IsAddHaarMeasure (s1004H (l := l) T b).measure :=
    (s1004H (l := l) T b).isAddHaar
  exact lt_of_le_of_lt (measure_mono (s1008Hull_subset_image_O (l := l) T b))
    ((s1008O_compact (l := l) T b).image (s1008E_continuous (l := l) T b)).measure_lt_top

#check s1008Hull_subset_image_O
#check s1008Hull_measure_lt_top

end LeanFormal.IUT.XiFPaper.S1008S1004HullFiniteActual

end