import tmp.sheaf.xif.paper.NativeTateLambertIntegralityActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # Integer a6 coefficient and its local-ring representative -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateA6IntegralityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality
open LeanFormal.IUT.XiFPaper.NativeTateS3IntegralityActual
open LeanFormal.IUT.XiFPaper.NativeTateLambertIntegralityActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

abbrev LF := localField (l := l) T b
abbrev LR := localRing (l := l) T b

lemma twelve_dvd_five_cube_add_seven_five (n : ℤ) :
    12 ∣ 5 * n ^ 3 + 7 * n ^ 5 := by
  have h : ((5 * n ^ 3 + 7 * n ^ 5 : ℤ) : ZMod 12) = 0 := by
    push_cast
    have hall : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
    exact hall (n : ZMod 12)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

noncomputable def a6Coeff (n : ℕ) : ℤ :=
  -(((5 * (n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 5) / 12))

lemma a6Coeff_mul_twelve (n : ℕ) :
    a6Coeff n * 12 = -(5 * (n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 5) := by
  unfold a6Coeff
  rw [neg_mul, Int.ediv_mul_cancel
    (twelve_dvd_five_cube_add_seven_five (n : ℤ))]

lemma a6Coeff_cast (n : ℕ) :
    ((a6Coeff n : ℤ) : LF (l := l) T b) =
      -((5 * (n : LF (l := l) T b) ^ 3 +
        7 * (n : LF (l := l) T b) ^ 5) / 12) := by
  have h := congrArg (fun z : ℤ => (z : LF (l := l) T b))
    (a6Coeff_mul_twelve n)
  push_cast at h ⊢
  calc
    ((a6Coeff n : ℤ) : LF (l := l) T b) =
        ((a6Coeff n : ℤ) : LF (l := l) T b) * 12 / 12 := by
          field_simp
    _ = (-(5 * (n : LF (l := l) T b) ^ 3 +
        7 * (n : LF (l := l) T b) ^ 5)) / 12 := by
          rw [h]
    _ = -((5 * (n : LF (l := l) T b) ^ 3 +
        7 * (n : LF (l := l) T b) ^ 5) / 12) := by ring

/-- Integral representative of the n-th a6 Lambert term. -/
noncomputable def a6TermR
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) :
    LR (l := l) T b :=
  if hn : 0 < n then
    (a6Coeff n : LR (l := l) T b) *
      qR (l := l) T b hq ^ n *
      ↑(((one_sub_q_pow_isUnit (l := l) T b hq n hn).unit)⁻¹ :
        (LR (l := l) T b)ˣ)
  else 0

theorem a6TermR_coe
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) (hn : 0 < n) :
    ((a6TermR (l := l) T b hq n : LR (l := l) T b) :
      LF (l := l) T b) =
      ((a6Coeff n : ℤ) : LF (l := l) T b) *
        q (l := l) T b ^ n / (1 - q (l := l) T b ^ n) := by
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
  simp [a6TermR, hn, qR_coe, hunit_coe, hinv, div_eq_mul_inv]

/-- Generic Lambert-term summability in the completion. -/
theorem lambertTermR_summable
    (hq : Valued.v (q (l := l) T b) < 1) (weight : ℕ) :
    Summable (fun n : ℕ => (lambertTermR (l := l) T b hq weight n :
      LF (l := l) T b)) := by
  have hqnorm : ‖q (l := l) T b‖ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff).mpr hq
  have hterm_eq : (fun n : ℕ => (lambertTermR (l := l) T b hq weight n :
      LF (l := l) T b)) =
      fun n : ℕ => (n : LF (l := l) T b) ^ weight *
        q (l := l) T b ^ n / (1 - q (l := l) T b ^ n) := by
    funext n
    by_cases hn : 0 < n
    · exact lambertTermR_coe (l := l) T b hq weight n hn
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      simp [lambertTermR]
  simpa [hterm_eq] using
    (TateCurve.lambertSeries_summable (K := LF (l := l) T b) weight hqnorm)

theorem a6TermR_hasSum
    (hq : Valued.v (q (l := l) T b) < 1) :
    HasSum (fun n : ℕ =>
      (a6TermR (l := l) T b hq n : LF (l := l) T b))
      (TateCurve.a6 (LF (l := l) T b) (q (l := l) T b)) := by
  let f : ℕ → LR (l := l) T b := a6TermR (l := l) T b hq
  have h3S : HasSum (fun n : ℕ =>
      (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b))
      (TateCurve.lambertSeries (LF (l := l) T b) 3 (q (l := l) T b)) := by
    rw [lambertTerm_sum_eq (l := l) T b hq 3]
    exact (lambertTermR_summable (l := l) T b hq 3).hasSum
  have h5S : HasSum (fun n : ℕ =>
      (lambertTermR (l := l) T b hq 5 n : LF (l := l) T b))
      (TateCurve.lambertSeries (LF (l := l) T b) 5 (q (l := l) T b)) := by
    rw [lambertTerm_sum_eq (l := l) T b hq 5]
    exact (lambertTermR_summable (l := l) T b hq 5).hasSum
  have hcomb : HasSum (fun n : ℕ =>
      -(5 * (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b) +
        7 * (lambertTermR (l := l) T b hq 5 n : LF (l := l) T b)) / 12)
      (TateCurve.a6 (LF (l := l) T b) (q (l := l) T b)) := by
    have h := (h3S.mul_left (-(5 / 12))).add
      (h5S.mul_left (-(7 / 12)))
    simpa [TateCurve.a6, div_eq_mul_inv, mul_add, add_mul, mul_assoc,
      mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using h
  have hterm_eq : (fun n : ℕ => (f n : LF (l := l) T b)) =
      fun n : ℕ => (-(5 *
        (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b)) + -(7 *
        (lambertTermR (l := l) T b hq 5 n : LF (l := l) T b))) / 12 := by
    funext n
    by_cases hn : 0 < n
    · rw [a6TermR_coe (l := l) T b hq n hn]
      rw [a6Coeff_cast (l := l) T b n]
      rw [lambertTermR_coe (l := l) T b hq 3 n hn]
      rw [lambertTermR_coe (l := l) T b hq 5 n hn]
      ring
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      simp [f, a6TermR, lambertTermR]
  rw [hterm_eq]
  convert hcomb using 1
  ext n
  ring

/-- The actual a6 q-series coefficient is integral. -/
theorem a6Integral
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ a : LR (l := l) T b,
      ((a : LR (l := l) T b) : LF (l := l) T b) =
        TateCurve.a6 (LF (l := l) T b) (q (l := l) T b) := by
  let f : ℕ → LR (l := l) T b := a6TermR (l := l) T b hq
  have h3S : HasSum (fun n : ℕ =>
      (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b))
      (TateCurve.lambertSeries (LF (l := l) T b) 3 (q (l := l) T b)) := by
    rw [lambertTerm_sum_eq (l := l) T b hq 3]
    exact (lambertTermR_summable (l := l) T b hq 3).hasSum
  have h5S : HasSum (fun n : ℕ =>
      (lambertTermR (l := l) T b hq 5 n : LF (l := l) T b))
      (TateCurve.lambertSeries (LF (l := l) T b) 5 (q (l := l) T b)) := by
    rw [lambertTerm_sum_eq (l := l) T b hq 5]
    exact (lambertTermR_summable (l := l) T b hq 5).hasSum
  have hcomb : HasSum (fun n : ℕ =>
      -(5 * (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b) +
        7 * (lambertTermR (l := l) T b hq 5 n : LF (l := l) T b)) / 12)
      (TateCurve.a6 (LF (l := l) T b) (q (l := l) T b)) := by
    have h := (h3S.mul_left (-(5 / 12))).add
      (h5S.mul_left (-(7 / 12)))
    simpa [TateCurve.a6, div_eq_mul_inv, mul_add, add_mul, mul_assoc,
      mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using h
  have hterm_eq : (fun n : ℕ => (f n : LF (l := l) T b)) =
      fun n : ℕ => -(5 *
        (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b) +
        7 * (lambertTermR (l := l) T b hq 5 n : LF (l := l) T b)) / 12 := by
    funext n
    by_cases hn : 0 < n
    · rw [a6TermR_coe (l := l) T b hq n hn]
      rw [a6Coeff_cast (l := l) T b n]
      rw [lambertTermR_coe (l := l) T b hq 3 n hn]
      rw [lambertTermR_coe (l := l) T b hq 5 n hn]
      ring
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      simp [f, a6TermR, lambertTermR]
  have hsum : HasSum (fun n : ℕ => (f n : LF (l := l) T b))
      (TateCurve.a6 (LF (l := l) T b) (q (l := l) T b)) := by
    simpa [hterm_eq] using hcomb
  have hlim : Filter.Tendsto
      (fun N : ℕ => (Finset.range N).sum
        (fun n => (f n : LF (l := l) T b)))
      Filter.atTop
      (nhds (TateCurve.a6 (LF (l := l) T b) (q (l := l) T b))) :=
    hsum.tendsto_sum_nat
  have hmem : TateCurve.a6 (LF (l := l) T b) (q (l := l) T b) ∈
      LR (l := l) T b :=
    localRing_tsum_mem (l := l) T b (f := f) hlim
  exact ⟨⟨_, hmem⟩, rfl⟩

end LeanFormal.IUT.XiFPaper.NativeTateA6IntegralityActual

end
