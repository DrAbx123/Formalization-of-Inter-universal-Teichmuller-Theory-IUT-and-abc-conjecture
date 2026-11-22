import tmp.sheaf.xif.paper.NativeTateQSquaresBasicIntegrality
import tmp.sheaf.xif.paper.NativeTateQSquaresIntegralityActual
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # s3 integrality from the closed integer subring -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateS3IntegralityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

noncomputable abbrev q : localField (l := l) T b :=
  (tateParameter (l := l) T b).q

/-- q as an element of the completion integers. -/
noncomputable def qR (hq : Valued.v (q (l := l) T b) < 1) :
    localRing (l := l) T b :=
  ⟨q (l := l) T b,
    (mem_adicCompletionIntegers
      (R := NumberField.RingOfIntegers T.arithmetic.F)
      (K := T.arithmetic.F)
      (v := localPrime (l := l) T b)).mpr hq.le⟩

@[simp] theorem qR_coe (hq : Valued.v (q (l := l) T b) < 1) :
    ((qR (l := l) T b hq : localRing (l := l) T b) :
      localField (l := l) T b) = q (l := l) T b := rfl

/-- q lies in the maximal ideal of the completion integers. -/
theorem qR_mem_maximalIdeal (hq : Valued.v (q (l := l) T b) < 1) :
    qR (l := l) T b hq ∈ IsLocalRing.maximalIdeal (localRing (l := l) T b) := by
  exact (ValuationSubring.valuation_lt_one_iff (localRing (l := l) T b) _).mpr
    ((Valuation.isEquiv_valuation_valuationSubring (v := Valued.v)).lt_one_iff_lt_one.mp hq)

/-- 1 - q^n is a unit in the completion integers. -/
theorem one_sub_q_pow_isUnit (hq : Valued.v (q (l := l) T b) < 1)
    (n : ℕ) (hn : 0 < n) :
    IsUnit (1 - qR (l := l) T b hq ^ n) := by
  have hmax : qR (l := l) T b hq ^ n ∈
      IsLocalRing.maximalIdeal (localRing (l := l) T b) :=
    Ideal.pow_mem_of_mem
      (I := IsLocalRing.maximalIdeal (localRing (l := l) T b))
      (a := qR (l := l) T b hq)
      (qR_mem_maximalIdeal (l := l) T b hq) n hn
  exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal (qR (l := l) T b hq ^ n)).mp hmax)

/-- The exact missing unit-family source for the Lambert denominator. -/
structure TateS3DenominatorUnitFamily
    (hq : Valued.v (q (l := l) T b) < 1) where
  denominatorUnit : ∀ n : ℕ, 0 < n →
    IsUnit (1 - qR (l := l) T b hq ^ n)

/-- Exact missing source object for the denominator units. -/
def TateS3DenominatorUnitFamilyRequired
    (hq : Valued.v (q (l := l) T b) < 1) : Prop :=
  Nonempty (TateS3DenominatorUnitFamily (l := l) T b hq)

/-- The actual denominator-unit family. -/
noncomputable def tateS3DenominatorUnitFamily
    (hq : Valued.v (q (l := l) T b) < 1) :
    TateS3DenominatorUnitFamily (l := l) T b hq where
  denominatorUnit := fun n hn => one_sub_q_pow_isUnit (l := l) T b hq n hn

/-- The denominator-unit source is actual. -/
theorem tateS3DenominatorUnitFamilyRequired
    (hq : Valued.v (q (l := l) T b) < 1) :
    TateS3DenominatorUnitFamilyRequired (l := l) T b hq :=
  ⟨tateS3DenominatorUnitFamily (l := l) T b hq⟩

/-- The integral representative of the n-th s3 Lambert term. -/
noncomputable def s3TermR
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) :
    localRing (l := l) T b :=
  if hn : 0 < n then
    (n : localRing (l := l) T b) ^ 3 *
      qR (l := l) T b hq ^ n *
      ↑(((one_sub_q_pow_isUnit (l := l) T b hq n hn).unit)⁻¹ :
        (localRing (l := l) T b)ˣ)
  else 0

/-- The integral representative of the n-th term has the expected value. -/
theorem s3TermR_coe
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) (hn : 0 < n) :
    ((s3TermR (l := l) T b hq n : localRing (l := l) T b) :
      localField (l := l) T b) =
      (n : localField (l := l) T b) ^ 3 * q (l := l) T b ^ n /
        (1 - q (l := l) T b ^ n) := by
  let h := one_sub_q_pow_isUnit (l := l) T b hq n hn
  have hunit_coe : ((h.unit : localRing (l := l) T b) :
      localField (l := l) T b) = 1 - q (l := l) T b ^ n := by
    rw [IsUnit.unit_spec]
    simp [qR_coe]
  have hinv : (((h.unit)⁻¹ : (localRing (l := l) T b)ˣ) :
      localField (l := l) T b) = (1 - q (l := l) T b ^ n)⁻¹ := by
    calc
      (((h.unit)⁻¹ : (localRing (l := l) T b)ˣ) :
          localField (l := l) T b) =
          ((((h.unit : localRing (l := l) T b)) :
            localField (l := l) T b))⁻¹ := by
            exact map_units_inv (algebraMap (localRing (l := l) T b)
              (localField (l := l) T b)) h.unit
      _ = (1 - q (l := l) T b ^ n)⁻¹ := by rw [hunit_coe]
  simp [s3TermR, hn, qR_coe, map_mul, map_pow, hunit_coe, hinv,
    div_eq_mul_inv]

/-- The Lambert s3 series is the tsum of the integral term representatives. -/
theorem s3_term_sum_eq
    (hq : Valued.v (q (l := l) T b) < 1) :
    TateCurve.lambertSeries (localField (l := l) T b) 3 (q (l := l) T b) =
      ∑' n : ℕ,
        ((s3TermR (l := l) T b hq n : localRing (l := l) T b) :
          localField (l := l) T b) := by
  have hqnorm : ‖q (l := l) T b‖ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff).mpr hq
  rw [TateCurve.lambertSeries_eq_sum_from_one (K := localField (l := l) T b) 3 hqnorm]
  apply tsum_congr
  intro n
  by_cases hn : 0 < n
  · rw [s3TermR_coe (l := l) T b hq n hn]
    simp [hn, div_eq_mul_inv]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp [s3TermR]

/-- The actual s3 integrality theorem. -/
theorem s3Integral
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ s : localRing (l := l) T b,
      ((s : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.lambertSeries (localField (l := l) T b) 3 (q (l := l) T b) := by
  let f : ℕ → localRing (l := l) T b := s3TermR (l := l) T b hq
  have hqnorm : ‖q (l := l) T b‖ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff).mpr hq
  have hterm_eq : (fun n : ℕ => (f n : localField (l := l) T b)) =
      fun n : ℕ => (n : localField (l := l) T b) ^ 3 *
        q (l := l) T b ^ n / (1 - q (l := l) T b ^ n) := by
    funext n
    by_cases hn : 0 < n
    · exact s3TermR_coe (l := l) T b hq n hn
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      simp [f, s3TermR]
  have hsummable : Summable (fun n : ℕ =>
      (f n : localField (l := l) T b)) := by
    simpa [hterm_eq] using
      (TateCurve.lambertSeries_summable (K := localField (l := l) T b) 3 hqnorm)
  have hsum : HasSum (fun n : ℕ => (f n : localField (l := l) T b))
      (TateCurve.lambertSeries (localField (l := l) T b) 3 (q (l := l) T b)) := by
    rw [s3_term_sum_eq (l := l) T b hq]
    exact hsummable.hasSum
  have hlim : Filter.Tendsto
      (fun N : ℕ => (Finset.range N).sum
        (fun n => (f n : localField (l := l) T b)))
      Filter.atTop
      (nhds (TateCurve.lambertSeries (localField (l := l) T b) 3
        (q (l := l) T b))) :=
    hsum.tendsto_sum_nat
  have hmem : TateCurve.lambertSeries (localField (l := l) T b) 3
      (q (l := l) T b) ∈ localRing (l := l) T b :=
    localRing_tsum_mem (l := l) T b (f := f) hlim
  exact ⟨⟨_, hmem⟩, rfl⟩

end LeanFormal.IUT.XiFPaper.NativeTateS3IntegralityActual

end
