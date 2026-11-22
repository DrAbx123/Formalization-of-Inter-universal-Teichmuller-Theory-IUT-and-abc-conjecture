import tmp.sheaf.xif.paper.UnitReferenceMeasureActual
import tmp.sheaf.xif.paper.S658RootNormalizedPaperSignedHullActual
import tmp.sheaf.xif.paper.HaarUnitFactorProof
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.MeasureTheory.Group.Measure

-- S662: normalized Haar measure for an arbitrary target average A.
-- Same exp scaling as NormalizedHaarHnormalActual; the resulting actual
-- IQHullLogVolumeInterface has canonical-hull log = ofReal A.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S662NormalizedHaarArbitraryAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open MeasureTheory

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

noncomputable def normalizedHaarScaleFor (A : Real) : Real :=
  Real.exp (A - arithmeticTupleHullUnitLogVolume places tuple -
    Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

theorem normalizedHaarScaleFor_pos (A : Real) :
    0 < normalizedHaarScaleFor places tuple mu A := Real.exp_pos _

noncomputable def normalizedHaarMeasureFor (A : Real) :
    Measure (ArithmeticTensorTupleBlock places tuple) :=
  (ENNReal.ofReal (normalizedHaarScaleFor places tuple mu A)) • mu

instance normalizedHaarMeasureFor_isAddHaar (A : Real) :
    Measure.IsAddHaarMeasure (normalizedHaarMeasureFor places tuple mu A) := by
  unfold normalizedHaarMeasureFor
  exact Measure.IsAddHaarMeasure.smul mu
    (ENNReal.ofReal_ne_zero_iff.mpr (normalizedHaarScaleFor_pos places tuple mu A))
    ENNReal.ofReal_ne_top

theorem normalizedHaarMeasureFor_unit_log (A : Real) :
    Real.log
        ((normalizedHaarMeasureFor places tuple mu A)
          (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      A - arithmeticTupleHullUnitLogVolume places tuple := by
  rw [normalizedHaarMeasureFor]
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (normalizedHaarScaleFor_pos places tuple mu A))]
  have hscale : normalizedHaarScaleFor places tuple mu A ≠ 0 :=
    ne_of_gt (normalizedHaarScaleFor_pos places tuple mu A)
  have hnu : (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal ≠ 0 :=
    ne_of_gt (unitReference_toReal_pos places tuple mu)
  rw [Real.log_mul hscale hnu]
  unfold normalizedHaarScaleFor
  rw [Real.log_exp]
  ring

theorem normalizedHaarMeasureFor_canonicalHull_log (A : Real) :
    Real.log
        ((normalizedHaarMeasureFor places tuple mu A)
          (arithmeticTupleCanonicalHull places tuple)).toReal = A := by
  rw [canonicalHullLog_eq_unitFactor (places := places) (tuple := tuple)
    (mu := normalizedHaarMeasureFor places tuple mu A)]
  rw [normalizedHaarMeasureFor_unit_log]
  ring

theorem normalizedHaarMeasureFor_interface_hnormal
    (A : Real) (hA : 0 <= A) :
    (arithmeticTupleIQHullLogVolumeInterface places tuple
        (normalizedHaarMeasureFor places tuple mu A)).logVolume
        (arithmeticTupleIQHullLogVolumeInterface places tuple
          (normalizedHaarMeasureFor places tuple mu A)).hull =
      ENNReal.ofReal A := by
  rw [arithmeticTupleIQHullLogVolumeInterface_logVolume,
    arithmeticTupleIQHullLogVolumeInterface_hull,
    haarLogVolume_of_lt_top
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple
      (normalizedHaarMeasureFor places tuple mu A)).1.2,
    normalizedHaarMeasureFor_canonicalHull_log]

theorem normalizedHaarMeasureFor_rootTheta_interface_hnormal
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    (arithmeticTupleIQHullLogVolumeInterface places tuple
        (normalizedHaarMeasureFor places tuple mu
          (rootThetaMagnitudeProcession T b).average)).logVolume
        (arithmeticTupleIQHullLogVolumeInterface places tuple
          (normalizedHaarMeasureFor places tuple mu
            (rootThetaMagnitudeProcession T b).average)).hull =
      ENNReal.ofReal (rootThetaMagnitudeProcession T b).average :=
  normalizedHaarMeasureFor_interface_hnormal places tuple mu
    (rootThetaMagnitudeProcession T b).average
    (rootThetaMagnitudeProcession_average_nonneg T b)

#check normalizedHaarMeasureFor
#check normalizedHaarMeasureFor_interface_hnormal

end LeanFormal.IUT.XiFPaper.S662NormalizedHaarArbitraryAverageActual

end