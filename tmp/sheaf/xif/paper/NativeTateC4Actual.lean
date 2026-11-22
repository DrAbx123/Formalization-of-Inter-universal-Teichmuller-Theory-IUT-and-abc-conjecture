import tmp.sheaf.xif.paper.NativeTateUnitOpenActual
import tmp.sheaf.xif.paper.NativeTateA6IntegralityActual
import tmp.sheaf.xif.paper.NativeTateLambertIntegralityActual

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateC4Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality
open LeanFormal.IUT.XiFPaper.NativeTateS3IntegralityActual
open LeanFormal.IUT.XiFPaper.NativeTateLambertIntegralityActual
open LeanFormal.IUT.XiFPaper.NativeTateA6IntegralityActual
open LeanFormal.IUT.XiFPaper.NativeTateUnitOpenActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

abbrev LF := localField (l := l) T b
abbrev LR := localRing (l := l) T b

theorem lambertTermR_mem_max
    (hq : Valued.v (q (l := l) T b) < 1) (weight n : ℕ) :
    lambertTermR (l := l) T b hq weight n ∈
      IsLocalRing.maximalIdeal (LR (l := l) T b) := by
  by_cases hn : 0 < n
  · have hqmax : qR (l := l) T b hq ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      qR_mem_maximalIdeal (l := l) T b hq
    have hqpow : qR (l := l) T b hq ^ n ∈
        IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      Ideal.pow_mem_of_mem
        (I := IsLocalRing.maximalIdeal (LR (l := l) T b))
        (a := qR (l := l) T b hq) hqmax n hn
    have hprod : (n : LR (l := l) T b) ^ weight *
        qR (l := l) T b hq ^ n ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      Ideal.mul_mem_left _ _ hqpow
    have hterm : (n : LR (l := l) T b) ^ weight *
        qR (l := l) T b hq ^ n *
          ↑(((one_sub_q_pow_isUnit (l := l) T b hq n hn).unit)⁻¹ :
            (LR (l := l) T b)ˣ) ∈
        IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      Ideal.mul_mem_right _ _ hprod
    simpa [lambertTermR, hn] using hterm
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp [lambertTermR]

theorem a6TermR_mem_max
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) :
    a6TermR (l := l) T b hq n ∈
      IsLocalRing.maximalIdeal (LR (l := l) T b) := by
  by_cases hn : 0 < n
  · have hqmax : qR (l := l) T b hq ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      qR_mem_maximalIdeal (l := l) T b hq
    have hqpow : qR (l := l) T b hq ^ n ∈
        IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      Ideal.pow_mem_of_mem
        (I := IsLocalRing.maximalIdeal (LR (l := l) T b))
        (a := qR (l := l) T b hq) hqmax n hn
    have hprod : ((a6Coeff n : ℤ) : LR (l := l) T b) *
        qR (l := l) T b hq ^ n ∈
        IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      Ideal.mul_mem_left _ _ hqpow
    have hterm : ((a6Coeff n : ℤ) : LR (l := l) T b) *
        qR (l := l) T b hq ^ n *
          ↑(((one_sub_q_pow_isUnit (l := l) T b hq n hn).unit)⁻¹ :
            (LR (l := l) T b)ˣ) ∈
        IsLocalRing.maximalIdeal (LR (l := l) T b) :=
      Ideal.mul_mem_right _ _ hprod
    simpa [a6TermR, hn] using hterm
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp [a6TermR]

theorem a6_mem_maximalIdeal
    (hq : Valued.v (q (l := l) T b) < 1) :
    TateCurve.a6 (LF (l := l) T b) (q (l := l) T b) ∈
      maximalIdealKSet (l := l) T b := by
  exact tsum_mem_maximalIdeal (l := l) T b
    (a6TermR_mem_max (l := l) T b hq)
    (a6TermR_hasSum (l := l) T b hq)

noncomputable def a4TermR
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) : LR (l := l) T b :=
  -5 * lambertTermR (l := l) T b hq 3 n

theorem a4TermR_mem_max
    (hq : Valued.v (q (l := l) T b) < 1) (n : ℕ) :
    a4TermR (l := l) T b hq n ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) := by
  exact Ideal.mul_mem_left _ _ (lambertTermR_mem_max (l := l) T b hq 3 n)

theorem a4_mem_maximalIdeal
    (hq : Valued.v (q (l := l) T b) < 1) :
    TateCurve.a4 (LF (l := l) T b) (q (l := l) T b) ∈
      maximalIdealKSet (l := l) T b := by
  have hsummable : Summable (fun n : ℕ =>
      (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b)) :=
    lambertTermR_summable (l := l) T b hq 3
  have h3 : HasSum (fun n : ℕ =>
      (lambertTermR (l := l) T b hq 3 n : LF (l := l) T b))
      (TateCurve.lambertSeries (LF (l := l) T b) 3
        (q (l := l) T b)) := by
    rw [lambertTerm_sum_eq (l := l) T b hq 3]
    exact hsummable.hasSum
  have h4 : HasSum (fun n : ℕ =>
      (a4TermR (l := l) T b hq n : LF (l := l) T b))
      (TateCurve.a4 (LF (l := l) T b) (q (l := l) T b)) := by
    have h := h3.mul_left
      ((algebraMap (LR (l := l) T b) (LF (l := l) T b))
        (-5 : LR (l := l) T b))
    have h5 : ((algebraMap (LR (l := l) T b) (LF (l := l) T b))
        (5 : LR (l := l) T b)) = (5 : LF (l := l) T b) :=
      map_ofNat (algebraMap (LR (l := l) T b) (LF (l := l) T b)) 5
    have hscalar : ((algebraMap (LR (l := l) T b) (LF (l := l) T b))
        (-5 : LR (l := l) T b)) = (-5 : LF (l := l) T b) := by
      rw [map_neg, h5]
    rw [hscalar] at h
    have hfun : (fun n : ℕ =>
        (a4TermR (l := l) T b hq n : LF (l := l) T b)) =
        (fun n : ℕ => -(5 *
          (lambertTermR (l := l) T b hq 3 n :
            LF (l := l) T b))) := by
      funext n
      change (algebraMap (LR (l := l) T b) (LF (l := l) T b))
        (a4TermR (l := l) T b hq n) = _
      simp [a4TermR, map_mul, map_neg, h5]
    rw [hfun]
    simpa [TateCurve.a4] using h
  exact tsum_mem_maximalIdeal (l := l) T b
    (a4TermR_mem_max (l := l) T b hq) h4

theorem a4_integral_mem
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ a4R : LR (l := l) T b,
      (a4R : LF (l := l) T b) = TateCurve.a4 (LF (l := l) T b) (q (l := l) T b) ∧
      a4R ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) := by
  have hx := a4_mem_maximalIdeal (l := l) T b hq
  rcases hx with ⟨hxR, hxnotunit⟩
  let a4R : LR (l := l) T b :=
    ⟨TateCurve.a4 (LF (l := l) T b) (q (l := l) T b), hxR⟩
  have hnotunit : ¬ IsUnit a4R := by
    intro hu
    exact hxnotunit ⟨a4R, hu, rfl⟩
  have hmax : a4R ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact mem_nonunits_iff.mpr hnotunit
  exact ⟨a4R, rfl, hmax⟩

theorem a6_integral_mem
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ a6R : LR (l := l) T b,
      (a6R : LF (l := l) T b) = TateCurve.a6 (LF (l := l) T b) (q (l := l) T b) ∧
      a6R ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) := by
  have hx := a6_mem_maximalIdeal (l := l) T b hq
  rcases hx with ⟨hxR, hxnotunit⟩
  let a6R : LR (l := l) T b :=
    ⟨TateCurve.a6 (LF (l := l) T b) (q (l := l) T b), hxR⟩
  have hnotunit : ¬ IsUnit a6R := by
    intro hu
    exact hxnotunit ⟨a6R, hu, rfl⟩
  have hmax : a6R ∈ IsLocalRing.maximalIdeal (LR (l := l) T b) := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact mem_nonunits_iff.mpr hnotunit
  exact ⟨a6R, rfl, hmax⟩

theorem c4_isUnit_and_valuation
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ c4R : LR (l := l) T b,
      IsUnit c4R ∧
      (c4R : LF (l := l) T b) =
        (TateCurve.weierstrassCurve (LF (l := l) T b) (q (l := l) T b)).c₄ ∧
      Valued.v (c4R : LF (l := l) T b) = 1 := by
  rcases a4_integral_mem (l := l) T b hq with ⟨a4R, ha4, hmax⟩
  have h48 : (48 : LR (l := l) T b) * a4R ∈
      IsLocalRing.maximalIdeal (LR (l := l) T b) :=
    Ideal.mul_mem_left _ _ hmax
  let c4R : LR (l := l) T b := 1 - 48 * a4R
  have hunit : IsUnit c4R := by
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal (48 * a4R)).mp h48)
  have hc4eq : (c4R : LF (l := l) T b) =
      (TateCurve.weierstrassCurve (LF (l := l) T b) (q (l := l) T b)).c₄ := by
    change (1 - 48 * (a4R : LF (l := l) T b)) = _
    rw [ha4]
    exact (TateCurve.canonical_c₄ (K := LF (l := l) T b) (q := q (l := l) T b)).symm
  have hval : Valued.v (c4R : LF (l := l) T b) = 1 := by
    exact (Valuation.valuationSubring.integers
      (v := Valued.v)).isUnit_iff_valuation_eq_one.mp hunit
  exact ⟨c4R, hunit, hc4eq, hval⟩

theorem discriminant_valuation_lt_one
    (hq : Valued.v (q (l := l) T b) < 1) :
    ∃ ΔR : LR (l := l) T b,
      (ΔR : LF (l := l) T b) =
        (TateCurve.weierstrassCurve (LF (l := l) T b) (q (l := l) T b)).Δ ∧
      Valued.v (ΔR : LF (l := l) T b) < 1 := by
  rcases a4_integral_mem (l := l) T b hq with ⟨a4R, ha4, h4max⟩
  rcases a6_integral_mem (l := l) T b hq with ⟨a6R, ha6, h6max⟩
  let I := IsLocalRing.maximalIdeal (LR (l := l) T b)
  have h4sq : a4R ^ 2 ∈ I :=
    Ideal.pow_mem_of_mem (I := I) (a := a4R) h4max 2 (by norm_num)
  have h4cube : a4R ^ 3 ∈ I :=
    Ideal.pow_mem_of_mem (I := I) (a := a4R) h4max 3 (by norm_num)
  have h6sq : a6R ^ 2 ∈ I :=
    Ideal.pow_mem_of_mem (I := I) (a := a6R) h6max 2 (by norm_num)
  have h4a6 : a4R * a6R ∈ I := by
    dsimp [I]
    exact Ideal.mul_mem_left _ _ h6max
  have h64 : (64 : LR (l := l) T b) * a4R ^ 3 ∈ I := by
    dsimp [I]
    exact Ideal.mul_mem_left _ _ h4cube
  have h432 : (432 : LR (l := l) T b) * a6R ^ 2 ∈ I := by
    dsimp [I]
    exact Ideal.mul_mem_left _ _ h6sq
  have h72 : (72 : LR (l := l) T b) * (a4R * a6R) ∈ I := by
    dsimp [I]
    exact Ideal.mul_mem_left _ _ h4a6
  let ΔR : LR (l := l) T b :=
    a4R ^ 2 - a6R - 64 * a4R ^ 3 - 432 * a6R ^ 2 + 72 * (a4R * a6R)
  have hΔmax : ΔR ∈ I := by
    dsimp [ΔR]
    apply Ideal.add_mem
    · apply Ideal.sub_mem
      · apply Ideal.sub_mem
        · apply Ideal.sub_mem
          · exact h4sq
          · exact h6max
        · exact h64
      · exact h432
    · exact h72
  have hΔeq : (ΔR : LF (l := l) T b) =
      (TateCurve.weierstrassCurve (LF (l := l) T b) (q (l := l) T b)).Δ := by
    change (a4R : LF (l := l) T b) ^ 2 -
      (a6R : LF (l := l) T b) -
      64 * (a4R : LF (l := l) T b) ^ 3 -
      432 * (a6R : LF (l := l) T b) ^ 2 +
      72 * ((a4R : LF (l := l) T b) * (a6R : LF (l := l) T b)) = _
    rw [ha4, ha6]
    have hcanon := (TateCurve.canonical_delta (K := LF (l := l) T b)
      (q := q (l := l) T b)).symm
    simpa [mul_assoc] using hcanon
  have hnotunit : ¬ IsUnit ΔR := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hΔmax
  have hvle : Valued.v (ΔR : LF (l := l) T b) ≤ 1 :=
    (Valuation.valuationSubring.integers (v := Valued.v)).map_le_one ΔR
  have hvne : Valued.v (ΔR : LF (l := l) T b) ≠ 1 := by
    intro hone
    exact hnotunit
      ((Valuation.valuationSubring.integers
        (v := Valued.v)).isUnit_iff_valuation_eq_one.mpr hone)
  exact ⟨ΔR, hΔeq, lt_of_le_of_ne hvle hvne⟩

end LeanFormal.IUT.XiFPaper.NativeTateC4Actual

end
