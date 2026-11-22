import tmp.sheaf.xif.paper.NativeTateS3IntegralityActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # General Lambert-term integrality (s5 and higher weights) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateLambertIntegralityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality
open LeanFormal.IUT.XiFPaper.NativeTateS3IntegralityActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

abbrev LF := localField (l := l) T b
abbrev LR := localRing (l := l) T b

noncomputable def lambertTermR
    (hq : Valued.v (q (l := l) T b) < 1) (weight n : ℕ) : LR (l := l) T b :=
  if hn : 0 < n then
    (n : LR (l := l) T b) ^ weight *
      qR (l := l) T b hq ^ n *
      ↑(((one_sub_q_pow_isUnit (l := l) T b hq n hn).unit)⁻¹ :
        (LR (l := l) T b)ˣ)
  else 0

theorem lambertTermR_coe
    (hq : Valued.v (q (l := l) T b) < 1) (weight : ℕ) (n : ℕ) (hn : 0 < n) :
    ((lambertTermR (l := l) T b hq weight n : LR (l := l) T b) :
      LF (l := l) T b) =
      (n : LF (l := l) T b) ^ weight * q (l := l) T b ^ n /
        (1 - q (l := l) T b ^ n) := by
  let h := one_sub_q_pow_isUnit (l := l) T b hq n hn
  have hunit_coe : ((h.unit : LR (l := l) T b) :
      LF (l := l) T b) = 1 - q (l := l) T b ^ n := by
    rw [IsUnit.unit_spec]
    simp [qR_coe]
  have hinv : (((h.unit)⁻¹ : (LR (l := l) T b)ˣ) :
      LF (l := l) T b) = (1 - q (l := l) T b ^ n)⁻¹ := by
    calc
      (((h.unit)⁻¹ : (LR (l := l) T b)ˣ) : LF (l := l) T b) =
          ((((h.unit : LR (l := l) T b)) : LF (l := l) T b))⁻¹ := by
            exact map_units_inv (algebraMap (LR (l := l) T b)
              (LF (l := l) T b)) h.unit
      _ = (1 - q (l := l) T b ^ n)⁻¹ := by rw [hunit_coe]
  simp [lambertTermR, hn, qR_coe, hunit_coe, hinv, div_eq_mul_inv]

theorem lambertTerm_sum_eq
    (hq : Valued.v (q (l := l) T b) < 1) (weight : ℕ) :
    TateCurve.lambertSeries (LF (l := l) T b) weight (q (l := l) T b) =
      ∑' n : ℕ,
        ((lambertTermR (l := l) T b hq weight n : LR (l := l) T b) :
          LF (l := l) T b) := by
  have hqnorm : ‖q (l := l) T b‖ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff).mpr hq
  rw [TateCurve.lambertSeries_eq_sum_from_one (K := LF (l := l) T b) weight hqnorm]
  apply tsum_congr
  intro n
  by_cases hn : 0 < n
  · rw [lambertTermR_coe (l := l) T b hq weight n hn]
    simp [hn, div_eq_mul_inv]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp [lambertTermR]

theorem lambertIntegral
    (hq : Valued.v (q (l := l) T b) < 1) (weight : ℕ) :
    ∃ s : LR (l := l) T b,
      ((s : LR (l := l) T b) : LF (l := l) T b) =
        TateCurve.lambertSeries (LF (l := l) T b) weight (q (l := l) T b) := by
  let f : ℕ → LR (l := l) T b :=
    lambertTermR (l := l) T b hq weight
  have hqnorm : ‖q (l := l) T b‖ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff).mpr hq
  have hterm_eq : (fun n : ℕ => (f n : LF (l := l) T b)) =
      fun n : ℕ => (n : LF (l := l) T b) ^ weight *
        q (l := l) T b ^ n / (1 - q (l := l) T b ^ n) := by
    funext n
    by_cases hn : 0 < n
    · exact lambertTermR_coe (l := l) T b hq weight n hn
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      simp [f, lambertTermR]
  have hsummable : Summable (fun n : ℕ =>
      (f n : LF (l := l) T b)) := by
    simpa [hterm_eq] using
      (TateCurve.lambertSeries_summable (K := LF (l := l) T b) weight hqnorm)
  have hsum : HasSum (fun n : ℕ => (f n : LF (l := l) T b))
      (TateCurve.lambertSeries (LF (l := l) T b) weight (q (l := l) T b)) := by
    rw [lambertTerm_sum_eq (l := l) T b hq weight]
    exact hsummable.hasSum
  have hlim : Filter.Tendsto
      (fun N : ℕ => (Finset.range N).sum
        (fun n => (f n : LF (l := l) T b)))
      Filter.atTop
      (nhds (TateCurve.lambertSeries (LF (l := l) T b) weight
        (q (l := l) T b))) := hsum.tendsto_sum_nat
  have hmem : TateCurve.lambertSeries (LF (l := l) T b) weight
      (q (l := l) T b) ∈ LR (l := l) T b := by
    simpa using localRing_tsum_mem (l := l) T b (f := f) hlim
  exact ⟨⟨_, hmem⟩, rfl⟩

/-- The actual a4 q-series coefficient is integral. -/
theorem a4Integral
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ a : LR (l := l) T b,
      ((a : LR (l := l) T b) : LF (l := l) T b) =
        TateCurve.a4 (LF (l := l) T b) (q (l := l) T b) := by
  rcases lambertIntegral (l := l) T b hq 3 with ⟨s, hs⟩
  refine ⟨-5 * s, ?_⟩
  rw [TateCurve.a4]
  change (algebraMap (LR (l := l) T b) (LF (l := l) T b)) (-5 * s) =
    -5 * TateCurve.lambertSeries (LF (l := l) T b) 3 (q (l := l) T b)
  simp only [map_mul, map_neg, map_ofNat]
  rw [show (algebraMap (LR (l := l) T b) (LF (l := l) T b)) s =
    TateCurve.lambertSeries (LF (l := l) T b) 3 (q (l := l) T b) from hs]

theorem s5Integral
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ s : LR (l := l) T b,
      ((s : LR (l := l) T b) : LF (l := l) T b) =
        TateCurve.lambertSeries (LF (l := l) T b) 5 (q (l := l) T b) :=
  lambertIntegral (l := l) T b hq 5

end LeanFormal.IUT.XiFPaper.NativeTateLambertIntegralityActual

end
