import tmp.sheaf.xif.paper.S2722Gap2AssemblyActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2720BridgeHaarActual
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2723CorrectedPointBoundActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2722Gap2AssemblyActual
open LeanFormal.IUT.XiFPaper.S2722HunitDActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- Corrected point bound: no hval.  For the S2586 Haar interface the point
singleton is null, so the bound is the nonnegativity of the weighted abc term. -/
theorem S2723_hpoint_singleton
    (eps : Real) (heps : 0 <= eps) :
    forall a n c : Nat, IsABCTriple a n c ->
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap (l := l) T b a n c)}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) := by
  intro a n c habc
  haveI : Module.IsTorsionFree ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) :=
    (Module.finBasis ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)).isTorsionFree
  haveI : Filter.NeBot
      (nhdsWithin (0 : qVFamTensorBlock T b) {(0 : qVFamTensorBlock T b)}ᶜ) :=
    Module.punctured_nhds_neBot ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) 0
  haveI : NullSingletonClass
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) :=
    MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass _
  have h0 : (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
        (S2588PointMap (l := l) T b a n c)} = 0 := by
    simpa [S2586IQHullLogVolumeInterface] using
      (MeasureTheory.NullSingletonClass.measure_singleton
        (x := S2586IQHullLogVolumeInterface (l := l) T b |>.scaleShift
          (S2588PointMap (l := l) T b a n c)))
  rw [h0]
  rw [ENNReal.toReal_zero]
  have hw : 0 <= (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
    mul_nonneg (by linarith) (arithmeticWeight_nonneg _)
  exact hw

/-- S2722 gap2 with corrected hpoint, no hval. -/
theorem S2723_gap2_no_hval
    (eps : Real) (heps : 0 < eps) :
    exists D : Real, forall a n c : Nat, IsABCTriple a n c ->
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
          (S2588PointMap (l := l) T b) a n c)).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            (S2586IQHullLogVolumeInterface (l := l) T b).hull).toReal + D :=
  S2722_gap2_with_D0 (l := l) T b eps
    (S2723_hpoint_singleton (l := l) T b eps (le_of_lt heps))

#check S2723_hpoint_singleton
#check S2723_gap2_no_hval
#print axioms S2723_hpoint_singleton
#print axioms S2723_gap2_no_hval

end LeanFormal.IUT.XiFPaper.S2723CorrectedPointBoundActual
end
