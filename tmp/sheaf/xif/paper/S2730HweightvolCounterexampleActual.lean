import tmp.sheaf.xif.paper.S2720BridgeHaarActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Geometry.FreyDiscriminantRadical
import Mathlib.Data.Nat.Prime.Infinite

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2730HweightvolCounterexampleActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
open LeanFormal.IUT.XiFPaper.S2720BridgeHaarActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

noncomputable abbrev S2730W : IQHullLogVolumeInterface (qVFamTensorBlock T b) :=
  S2586IQHullLogVolumeInterface (l := l) T b

/-- The S2586 comparison region has log-volume bounded by the fixed unit-region
log-volume: scaleShift is the identity and the point has zero Haar measure. -/
theorem S2730_region_logVolume_le_unit (a n c : Nat) :
    (S2730W (l := l) T b).logVolume (normalizedComparisonRegion W (S2588PointMap T b) a n c)
      ≤ (S2730W (l := l) T b).logVolume (S2730W (l := l) T b).unitRegion := by
  have hnull : (S2730W (l := l) T b).logVolume {(S2730W (l := l) T b).scaleShift (S2588PointMap T b a n c)} = 0 :=
    S2590SingletonNull (l := l) T b ((S2730W (l := l) T b).scaleShift (S2588PointMap T b a n c))
  have hsplit :
      (S2730W (l := l) T b).logVolume (normalizedComparisonRegion W (S2588PointMap T b) a n c)
        ≤ (S2730W (l := l) T b).logVolume ((S2730W (l := l) T b).scaleShift '' (S2730W (l := l) T b).unitRegion) +
          (S2730W (l := l) T b).logVolume {(S2730W (l := l) T b).scaleShift (S2588PointMap T b a n c)} := by
    rw [normalizedComparisonRegion, Set.image_union, Set.image_singleton]
    exact measure_union_le _ _
  calc
    (S2730W (l := l) T b).logVolume (normalizedComparisonRegion W (S2588PointMap T b) a n c)
        ≤ (S2730W (l := l) T b).logVolume ((S2730W (l := l) T b).scaleShift '' (S2730W (l := l) T b).unitRegion) +
          (S2730W (l := l) T b).logVolume {(S2730W (l := l) T b).scaleShift (S2588PointMap T b a n c)} := hsplit
    _ = (S2730W (l := l) T b).logVolume ((S2730W (l := l) T b).scaleShift '' (S2730W (l := l) T b).unitRegion) := by rw [hnull, add_zero]
    _ ≤ (S2730W (l := l) T b).logVolume (S2730W (l := l) T b).unitRegion := (S2730W (l := l) T b).scaleShift_unitRegion_logVolume_le

/-- Fixed-scale hweightvol counterexample at the actual S2586 carrier: for a
sufficiently large prime ABC triple, the arithmetic weight exceeds the fixed
unit-region log-volume, hence exceeds the comparison-region log-volume. -/
theorem S2730_hweightvol_counterexample :
    ¬ (∀ a n c : Nat, IsABCTriple a n c →
        arithmeticWeight (abcRationalPoint a c) ≤
          ((S2730W (l := l) T b).logVolume (normalizedComparisonRegion W (S2588PointMap T b) a n c)).toReal) := by
  intro h
  let B : Real := ((S2730W (l := l) T b).logVolume (S2730W (l := l) T b).unitRegion).toReal
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp B)
  have hnpos : (0 : Real) < (n : Real) := lt_trans (Real.exp_pos B) hn
  have hlogN : B < Real.log (n : Real) := by
    have hh := Real.log_lt_log (Real.exp_pos B) hn
    simpa using hh
  obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes n
  have hp2 : 2 ≤ p := hp.two_le
  have hlogP : B < Real.log (p : Real) := by
    have hnp : (n : Real) ≤ (p : Real) := by exact_mod_cast hpn
    exact lt_of_lt_of_le hlogN (Real.log_le_log hnpos hnp)
  have hp1 : 1 ≤ p := hp.one_lt.le
  have habc : IsABCTriple 1 (p - 1) p := by
    refine ⟨by norm_num, by omega, by omega, Nat.coprime_one_left _⟩
  have hweight : Real.log (p : Real) ≤ arithmeticWeight (abcRationalPoint 1 p) := by
    rw [LeanFormal.IUT.arithmeticWeight_abcRationalPoint habc]
    have hpne : (1 * (p - 1) * p) ≠ 0 := by omega
    have hdiv : p ∣ natRadical (1 * (p - 1) * p) :=
      (prime_dvd_natRadical_iff hp hpne).mpr (by
        refine ⟨1 * (p - 1), ?_⟩
        ring)
    have hle : p ≤ natRadical (1 * (p - 1) * p) :=
      Nat.le_of_dvd (natRadical_pos _) hdiv
    have hpos : (0 : Real) < (p : Real) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp2)
    exact Real.log_le_log hpos (by exact_mod_cast hle)
  have hregion := S2730_region_logVolume_le_unit (l := l) T b 1 (p - 1) p
  have hregionTo :
      ((S2730W (l := l) T b).logVolume (normalizedComparisonRegion W (S2588PointMap T b) 1 (p - 1) p)).toReal
        ≤ B := by
    exact ENNReal.toReal_mono (ne_of_lt (S2730W (l := l) T b).unitRegion_logVolume_lt_top) hregion
  have hbound := h 1 (p - 1) p habc
  linarith

#check S2730_region_logVolume_le_unit
#check S2730_hweightvol_counterexample
#print axioms S2730_hweightvol_counterexample
end LeanFormal.IUT.XiFPaper.S2730HweightvolCounterexampleActual
end
