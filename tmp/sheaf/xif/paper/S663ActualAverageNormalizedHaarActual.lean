import tmp.sheaf.xif.paper.S658RootNormalizedPaperSignedHullActual
import tmp.sheaf.n8.closure.C6ActualIQData
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S663ActualAverageNormalizedHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open MeasureTheory
open scoped BigOperators

universe ua uv uK uW uX
variable {l : PrimeGeFive}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota → Type uW}
variable (places : (i : iota) → W i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Normalization scale for an arbitrary target average. -/
noncomputable def s663Scale (a : Real) : Real :=
  Real.exp (a - arithmeticTupleHullUnitLogVolume places tuple -
    Real.log (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

theorem s663Scale_pos (a : Real) :
    0 < s663Scale (K := K) (p := p) places tuple nu a :=
  Real.exp_pos _

/-- The normalized Haar measure with arbitrary target average. -/
noncomputable def s663Measure (a : Real) :
    Measure (ArithmeticTensorTupleBlock places tuple) :=
  (ENNReal.ofReal (s663Scale (K := K) (p := p) places tuple nu a)) • nu

instance s663Measure_isAddHaar (a : Real) :
    Measure.IsAddHaarMeasure (s663Measure (K := K) (p := p) places tuple nu a) := by
  unfold s663Measure
  exact Measure.IsAddHaarMeasure.smul nu
    (c := ENNReal.ofReal (s663Scale (K := K) (p := p) places tuple nu a))
    (ENNReal.ofReal_ne_zero_iff.mpr
      (s663Scale_pos (K := K) (p := p) places tuple nu a))
    ENNReal.ofReal_ne_top

theorem s663Measure_unit_toReal (a : Real) :
    ((s663Measure (K := K) (p := p) places tuple nu a)
      (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      s663Scale (K := K) (p := p) places tuple nu a *
        (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
  unfold s663Measure
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (s663Scale_pos (K := K) (p := p) places tuple nu a))]

theorem s663Measure_unit_log (a : Real) :
    Real.log ((s663Measure (K := K) (p := p) places tuple nu a)
      (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      a - arithmeticTupleHullUnitLogVolume places tuple := by
  rw [s663Measure_unit_toReal]
  have hscale : s663Scale (K := K) (p := p) places tuple nu a ≠ 0 :=
    ne_of_gt (s663Scale_pos (K := K) (p := p) places tuple nu a)
  have hnu : (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple nu).2.1.ne' (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple nu).2.2.ne)
  rw [Real.log_mul hscale hnu]
  unfold s663Scale
  rw [Real.log_exp]
  ring

/-- The actual IQ interface with arbitrary target average. -/
noncomputable def s663Interface (a : Real) :
    IQHullLogVolumeInterface (ArithmeticTensorTupleBlock places tuple) :=
  (C6ActualIQData.actual places tuple
    (s663Measure (K := K) (p := p) places tuple nu a)).iqInterface

theorem s663Interface_hull (a : Real) :
    (s663Interface (K := K) (p := p) places tuple nu a).hull =
      arithmeticTupleCanonicalHull places tuple := by
  unfold s663Interface C6ActualIQData.actual
  simp

theorem s663Interface_logVolume_hull (a : Real) :
    (s663Interface (K := K) (p := p) places tuple nu a).logVolume
      (s663Interface (K := K) (p := p) places tuple nu a).hull =
      ENNReal.ofReal a := by
  unfold s663Interface C6ActualIQData.actual
  change (arithmeticTupleIQHullLogVolumeInterface (K := K) (p := p) places tuple
    (s663Measure (K := K) (p := p) places tuple nu a)).logVolume
    (arithmeticTupleIQHullLogVolumeInterface (K := K) (p := p) places tuple
      (s663Measure (K := K) (p := p) places tuple nu a)).hull = ENNReal.ofReal a
  rw [arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_eq_ofReal]
  rw [s663Measure_unit_log]
  ring

/-- The arbitrary target average used by S663. -/
noncomputable def s663Average : Real :=
  (rootThetaMagnitudeProcession T b).average

/-- The actual PaperSignedHull with A and hnormal filled by the normalized Haar. -/
noncomputable def s663PaperSignedHull :
    PaperSignedHull (ArithmeticTensorTupleBlock places tuple) (SignedLabel l.value) :=
  S658RootNormalizedPaperSignedHullActual.rootNormalizedPaperSignedHullCorrected T b
    (s663Interface (K := K) (p := p) places tuple nu (s663Average T b))
    (s663Interface_logVolume_hull (K := K) (p := p) places tuple nu (s663Average T b))

theorem s663PaperSignedHull_signed_eq :
    (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b).signedHullLogVolume =
      -(rootThetaMagnitudeProcession T b).average := by
  unfold s663PaperSignedHull s663Average
  exact S658RootNormalizedPaperSignedHullActual.rootNormalizedPaperSignedHullCorrected_signed_eq T b
    (s663Interface (K := K) (p := p) places tuple nu
      (rootThetaMagnitudeProcession T b).average)
    (s663Interface_logVolume_hull (K := K) (p := p) places tuple nu
      (rootThetaMagnitudeProcession T b).average)

end LeanFormal.IUT.XiFPaper.S663ActualAverageNormalizedHaarActual

end
