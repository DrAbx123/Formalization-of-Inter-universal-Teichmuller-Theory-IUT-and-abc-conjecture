import tmp.sheaf.xif.paper.Mzk1Lemma23SeparationActual
import tmp.sheaf.xif.paper.Mzk1MoebiusP1CActual

/-!
# Mzk1Lemma23ExplicitActual — explicit Möbius separation of paper [Mzk1] Lemma 2.3

Paper position.  [Mzk1] Lemma 2.3 (source lines 163-165) separates a point `beta` from a
finite set `S` on `P^1` by a Möbius transformation: for a fixed rational `C > 0` there is a
Möbius map `N` with `N(beta) = C`, `|N(alpha)| <= 1` for `alpha in S` and `N(infinity) = 0`.
The user-supplied proof is completely explicit:

* `delta = min_{alpha in S} |beta - alpha| > 0` (`1` if `S` is empty), because `S` is
  finite and `beta` is not in `S`;
* choose a rational `eps > 0` with `(C+1) eps <= delta`;
* put `lam = beta + eps` and `N(x) = C eps / (lam - x)`.

Then `N(beta) = C`; for `alpha in S` we have
`|lam - alpha| >= |beta - alpha| - eps >= delta - eps >= C eps`, hence
`|N(alpha)| <= 1`; the denominator `lam - x` is nonzero at `x = beta` and at every
`x in S`; the Möbius matrix of `N` is `[[0, C eps], [-1, lam]]` with determinant
`C eps != 0`, so `N` has a pole at `lam` (mapping `lam` to infinity) and maps
`infinity` to `0`.

This file proves all of the above over `Q`, with no `sorry` and no new axioms.  It imports
`Mzk1Lemma23SeparationActual` (for the rational `sepValue` bridge) and
`Mzk1MoebiusP1CActual` (for the `P^1`/Möbius vocabulary and the pole/infinity
conventions of `MoebiusData.mapPoints`).

CONTENTS (all proved):
* `sepDelta` with `sepDelta_pos`, `sepDelta_le`;
* `exists_eps_pos_le`, `exists_eps_le`;
* `sepLam`, `sepN`, `sepN_eq_div`;
* `separation_explicit_beta` (`N beta = C`), `separation_explicit_alpha` (`|N alpha| <= 1`);
* `separation_denominator_ne_zero`, `separation_lam_notin`, `sepLam_ne_beta`;
* `separation_strict` (for `C > 1`: `beta` is strictly closer to `lam` than `S`);
* `sepN_eq_neg_mul_sepValue`, `separation_sepValue_alpha` (bridge to `sepValue`);
* `exists_explicit_separation` (combined), the `C = 4` specialization `separation_C4`,
  and the `sepValue`-shaped combined statement `exists_sepValue_bounds`;
* `sepMoebius` with `sepMoebius_matrix`, `sepMoebius_det`, and the `P^1` values
  `sepMoebius_mapPoints_beta`, `sepMoebius_mapPoints_lam` (pole), `sepMoebius_mapPoints_infty`,
  `sepMoebius_mapPoints_alpha`, `sepMoebius_mapPoints_alpha_ne_infty`.

Allowed axioms: only `propext`, `Classical.choice`, `Quot.sound` (through `Finset.min'`
and Mathlib).  No closure of the paper's `Qbar`/`C` statement is claimed here; that
paper-scope statement remains a named statement in `Mzk1Lemma23SeparationActual`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma23ExplicitActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1CActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma23SeparationActual

/-! ## The separation centre and the explicit separation value -/

/-- The separation centre `lam = beta + eps` of paper [Mzk1] Lemma 2.3. -/
def sepLam (β eps : ℚ) : ℚ := β + eps

/-- The explicit separation value `N(x) = C eps / (lam - x)`, where `lam = beta + eps`
(the Möbius transformation of paper [Mzk1] Lemma 2.3, with pole at `lam`). -/
def sepN (C eps β x : ℚ) : ℚ := (C * eps) / (β + eps - x)

/-- Definitional form of `sepLam`. -/
theorem sepLam_eq (β eps : ℚ) : sepLam β eps = β + eps := rfl

/-- Definitional form of `sepN`. -/
theorem sepN_eq_div (C eps β x : ℚ) : sepN C eps β x = (C * eps) / (β + eps - x) := rfl

/-! ## The distance `delta` from `beta` to `S` -/

/-- The minimum of `|beta - alpha|` over `alpha in S`, defined to be `1` when `S` is
empty.  For `beta` outside the finite set `S` it is a positive rational lower bound for
the distance from `beta` to `S`. -/
def sepDelta (S : Finset ℚ) (β : ℚ) : ℚ :=
  if h : S.card = 0 then 1
  else (S.image (fun α => |β - α|)).min'
    ((Finset.card_pos.mp (Nat.pos_of_ne_zero h)).image _)

/-- `sepDelta` is positive for `beta` outside `S`. -/
theorem sepDelta_pos (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) : 0 < sepDelta S β := by
  unfold sepDelta
  split_ifs with h
  · norm_num
  · have hmem : (S.image (fun α => |β - α|)).min'
        ((Finset.card_pos.mp (Nat.pos_of_ne_zero h)).image _) ∈
          S.image (fun α => |β - α|) := Finset.min'_mem _ _
    obtain ⟨α0, hα0, hδeq⟩ := Finset.mem_image.mp hmem
    have hpos : 0 < |β - α0| := abs_pos.mpr (sub_ne_zero.mpr (fun hh => hβ (hh ▸ hα0)))
    rw [← hδeq]
    exact hpos

/-- `sepDelta` never exceeds the distance from `beta` to a point of `S`. -/
theorem sepDelta_le (S : Finset ℚ) (β : ℚ) {α : ℚ} (hα : α ∈ S) :
    sepDelta S β ≤ |β - α| := by
  unfold sepDelta
  split_ifs with h
  · exfalso
    have hS : S = ∅ := Finset.card_eq_zero.mp h
    rw [hS] at hα
    exact absurd hα (by simp)
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨α, hα, rfl⟩)

/-! ## Choosing `eps` -/

/-- For any positive rational `delta` and `C > 0` there is a positive rational `eps` with
`(C+1) eps <= delta` (take `eps = delta / (2 (C+1))`). -/
theorem exists_eps_pos_le (C δ : ℚ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ eps : ℚ, 0 < eps ∧ (C + 1) * eps ≤ δ := by
  have hC1 : (0 : ℚ) < C + 1 := by linarith
  have hC1ne : (C + 1) ≠ 0 := ne_of_gt hC1
  refine ⟨δ / (2 * (C + 1)), ?_, ?_⟩
  · have h2 : (0 : ℚ) < 2 * (C + 1) := by linarith
    exact div_pos hδ h2
  · have h : (C + 1) * (δ / (2 * (C + 1))) = δ / 2 := by
      rw [← mul_div_assoc, mul_comm (C + 1) δ]
      exact mul_div_mul_right δ 2 hC1ne
    rw [h]
    linarith

/-- The explicit `eps` choice for the distance `sepDelta S beta`. -/
theorem exists_eps_le (S : Finset ℚ) (β C : ℚ) (hβ : β ∉ S) (hC : 0 < C) :
    ∃ eps : ℚ, 0 < eps ∧ (C + 1) * eps ≤ sepDelta S β :=
  exists_eps_pos_le C (sepDelta S β) hC (sepDelta_pos S β hβ)

/-! ## Values of the explicit separation function -/

/-- `N(beta) = C`. -/
theorem separation_explicit_beta (C eps β : ℚ) (heps : eps ≠ 0) :
    sepN C eps β β = C := by
  rw [sepN_eq_div]
  have h : β + eps - β = eps := by ring
  rw [h]
  exact mul_div_cancel_right₀ C heps

/-- `|N(alpha)| <= 1` for every `alpha in S`. -/
theorem separation_explicit_alpha (S : Finset ℚ) (β C eps : ℚ) (hβ : β ∉ S)
    (hC : 0 < C) (heps : 0 < eps) (hbound : (C + 1) * eps ≤ sepDelta S β) :
    ∀ α ∈ S, |sepN C eps β α| ≤ 1 := by
  intro α hα
  have hδle : sepDelta S β ≤ |β - α| := sepDelta_le S β hα
  have hCeps : (0 : ℚ) < C * eps := mul_pos hC heps
  have htri : |β - α| ≤ |β + eps - α| + eps := by
    have h := abs_add_le (β + eps - α) (-eps)
    have heq : (β + eps - α) + -eps = β - α := by ring
    rw [heq, abs_neg, abs_of_pos heps] at h
    exact h
  have hden : C * eps ≤ |β + eps - α| := by nlinarith [hbound, hδle, htri]
  have hN : |sepN C eps β α| = (C * eps) / |β + eps - α| := by
    rw [sepN_eq_div, abs_div, abs_of_pos hCeps]
  rw [hN]
  have hpos : (0 : ℚ) < |β + eps - α| := lt_of_lt_of_le hCeps hden
  rw [div_le_one hpos]
  exact hden

/-- The denominator `lam - x = beta + eps - x` never vanishes on `S` nor at `x = beta`. -/
theorem separation_denominator_ne_zero (S : Finset ℚ) (β C eps : ℚ) (hβ : β ∉ S)
    (hC : 0 < C) (heps : 0 < eps) (hbound : (C + 1) * eps ≤ sepDelta S β) :
    (∀ α ∈ S, β + eps - α ≠ 0) ∧ β + eps - β ≠ 0 := by
  have hCeps : (0 : ℚ) < C * eps := mul_pos hC heps
  constructor
  · intro α hα hzero
    have hδle : sepDelta S β ≤ |β - α| := sepDelta_le S β hα
    have hval : |β - α| = eps := by
      have h : β - α = -eps := by linarith
      rw [h, abs_neg, abs_of_pos heps]
    have hle : (C + 1) * eps ≤ eps := by
      calc (C + 1) * eps ≤ sepDelta S β := hbound
        _ ≤ |β - α| := hδle
        _ = eps := hval
    nlinarith [hCeps, hle]
  · intro h
    have he : eps = 0 := by linarith
    exact heps.ne' he

/-- The centre `lam = beta + eps` is outside `S`. -/
theorem separation_lam_notin (S : Finset ℚ) (β C eps : ℚ) (hβ : β ∉ S) (hC : 0 < C)
    (heps : 0 < eps) (hbound : (C + 1) * eps ≤ sepDelta S β) :
    sepLam β eps ∉ S := by
  intro hmem
  have h := (separation_denominator_ne_zero S β C eps hβ hC heps hbound).1
    (sepLam β eps) hmem
  apply h
  unfold sepLam
  ring

/-- The centre `lam = beta + eps` is not `beta`. -/
theorem sepLam_ne_beta (β eps : ℚ) (heps : eps ≠ 0) : sepLam β eps ≠ β := by
  unfold sepLam
  intro h
  exact heps (by linarith)

/-- For `C > 1`, `beta` is strictly closer to `lam = beta + eps` than every point of `S`. -/
theorem separation_strict (S : Finset ℚ) (β C eps : ℚ) (hβ : β ∉ S) (hC : 1 < C)
    (heps : 0 < eps) (hbound : (C + 1) * eps ≤ sepDelta S β) :
    ∀ α ∈ S, |β - sepLam β eps| < |α - sepLam β eps| := by
  intro α hα
  have hδle : sepDelta S β ≤ |β - α| := sepDelta_le S β hα
  have htri : |β - α| ≤ |β + eps - α| + eps := by
    have h := abs_add_le (β + eps - α) (-eps)
    have heq : (β + eps - α) + -eps = β - α := by ring
    rw [heq, abs_neg, abs_of_pos heps] at h
    exact h
  have hdenC : C * eps ≤ |β + eps - α| := by nlinarith [hbound, hδle, htri]
  have h1lt : eps < C * eps := by
    have hpos : (0 : ℚ) < C - 1 := by linarith
    have h := mul_pos hpos heps
    nlinarith [h]
  have hlt : eps < |β + eps - α| := by linarith
  have hβval : |β - sepLam β eps| = eps := by
    have h : β - sepLam β eps = -eps := by unfold sepLam; ring
    rw [h, abs_neg, abs_of_pos heps]
  have hαval : |α - sepLam β eps| = |β + eps - α| := by
    have h : α - sepLam β eps = -(β + eps - α) := by unfold sepLam; ring
    rw [h, abs_neg]
  rw [hβval, hαval]
  exact hlt

/-! ## Bridge to the `sepValue` of `Mzk1Lemma23SeparationActual` -/

/-- `N` is `-(C eps)` times `sepValue lam`, with `lam = beta + eps`. -/
theorem sepN_eq_neg_mul_sepValue (C eps β x : ℚ) :
    sepN C eps β x = (-(C * eps)) * sepValue (sepLam β eps) x := by
  have h1 : sepN C eps β x = (C * eps) * (β + eps - x)⁻¹ := by
    rw [sepN_eq_div, div_eq_mul_inv]
  have h2 : (β + eps - x)⁻¹ = -((x - sepLam β eps)⁻¹) := by
    have h : β + eps - x = -(x - sepLam β eps) := by unfold sepLam; ring
    rw [h, inv_neg]
  have h3 : sepValue (sepLam β eps) x = (x - sepLam β eps)⁻¹ := rfl
  rw [h1, h2, h3]
  ring

/-- In `sepValue` form: `|(lam - alpha)^{-1}| <= 1/(C eps)` for `alpha in S`. -/
theorem separation_sepValue_alpha (S : Finset ℚ) (β C eps : ℚ) (hβ : β ∉ S)
    (hC : 0 < C) (heps : 0 < eps) (hbound : (C + 1) * eps ≤ sepDelta S β) :
    ∀ α ∈ S, |sepValue (sepLam β eps) α| ≤ 1 / (C * eps) := by
  intro α hα
  have hN : |sepN C eps β α| ≤ 1 :=
    separation_explicit_alpha S β C eps hβ hC heps hbound α hα
  have habs : |sepN C eps β α| = (C * eps) * |sepValue (sepLam β eps) α| := by
    rw [sepN_eq_neg_mul_sepValue, abs_mul, abs_neg, abs_of_pos (mul_pos hC heps)]
  rw [habs] at hN
  rw [le_div_iff₀ (mul_pos hC heps), mul_comm]
  linarith

/-! ## Combined statements -/

/-- Combined explicit separation statement (paper [Mzk1] Lemma 2.3, rational form): for
`beta` outside a finite `S` and any rational `C > 1` there is a rational `eps > 0` with
`(C+1) eps <= sepDelta S beta`, `N(beta) = C`, `|N(alpha)| <= 1` on `S`, the centre
`lam = beta + eps` outside `S` and different from `beta`, and `beta` strictly closer to
`lam` than every `alpha in S`. -/
theorem exists_explicit_separation (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) (C : ℚ)
    (hC : 1 < C) :
    ∃ eps : ℚ, 0 < eps ∧ (C + 1) * eps ≤ sepDelta S β ∧ sepN C eps β β = C ∧
      (∀ α ∈ S, |sepN C eps β α| ≤ 1) ∧ sepLam β eps ∉ S ∧ sepLam β eps ≠ β ∧
      (∀ α ∈ S, |β - sepLam β eps| < |α - sepLam β eps|) := by
  have hC0 : (0 : ℚ) < C := by linarith
  obtain ⟨eps, heps, hbound⟩ := exists_eps_le S β C hβ hC0
  exact ⟨eps, heps, hbound, separation_explicit_beta C eps β heps.ne',
    separation_explicit_alpha S β C eps hβ hC0 heps hbound,
    separation_lam_notin S β C eps hβ hC0 heps hbound,
    sepLam_ne_beta β eps heps.ne',
    separation_strict S β C eps hβ hC heps hbound⟩

/-- The paper's constant `C = 4` specialization of the explicit separation. -/
theorem separation_C4 (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ eps : ℚ, 0 < eps ∧ 5 * eps ≤ sepDelta S β ∧ sepN 4 eps β β = 4 ∧
      (∀ α ∈ S, |sepN 4 eps β α| ≤ 1) ∧ sepLam β eps ∉ S ∧ sepLam β eps ≠ β ∧
      (∀ α ∈ S, |β - sepLam β eps| < |α - sepLam β eps|) := by
  obtain ⟨eps, heps, hbound, hβC, hα, hlamS, hlamβ, hstrict⟩ :=
    exists_explicit_separation S β hβ 4 (by norm_num)
  have hbound' : 5 * eps ≤ sepDelta S β := by
    have h : (4 : ℚ) + 1 = 5 := by norm_num
    rwa [h] at hbound
  exact ⟨eps, heps, hbound', hβC, hα, hlamS, hlamβ, hstrict⟩

/-- Combined statements in `sepValue` form (paper [Mzk1] Lemma 2.3, rational version): for
`beta` outside a finite `S` and any rational `C > 1` there are rationals `lam` and `c > 0` with
`lam` outside `S`, `lam != beta`, `sepValue lam beta != 0`, the bound
`|sepValue lam alpha| <= 1/c` on `S`, and `beta` strictly closer to `lam` than every
`alpha in S` (equivalently `|sepValue lam alpha| < |sepValue lam beta|` on `S`). -/
theorem exists_sepValue_bounds (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) (C : ℚ) (hC : 1 < C) :
    ∃ lam : ℚ, ∃ c : ℚ, 0 < c ∧ lam ∉ S ∧ lam ≠ β ∧ sepValue lam β ≠ 0 ∧
      (∀ α ∈ S, |sepValue lam α| ≤ 1 / c) ∧
      (∀ α ∈ S, |sepValue lam α| < |sepValue lam β|) := by
  have hC0 : (0 : ℚ) < C := by linarith
  obtain ⟨eps, heps, hbound⟩ := exists_eps_le S β C hβ hC0
  have hlamS : sepLam β eps ∉ S := separation_lam_notin S β C eps hβ hC0 heps hbound
  have hlamβ : sepLam β eps ≠ β := sepLam_ne_beta β eps heps.ne'
  have hcpos : (0 : ℚ) < C * eps := mul_pos hC0 heps
  have hsv : ∀ α ∈ S, |sepValue (sepLam β eps) α| ≤ 1 / (C * eps) :=
    separation_sepValue_alpha S β C eps hβ hC0 heps hbound
  refine ⟨sepLam β eps, C * eps, hcpos, hlamS, hlamβ, ?_, hsv, ?_⟩
  · have h : β - sepLam β eps ≠ 0 := sub_ne_zero.mpr (Ne.symm hlamβ)
    simpa [sepValue] using inv_ne_zero h
  · intro α hα
    have hstrict : |β - sepLam β eps| < |α - sepLam β eps| :=
      separation_strict S β C eps hβ hC heps hbound α hα
    have hbpos : 0 < |β - sepLam β eps| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hlamβ))
    have hapos : 0 < |α - sepLam β eps| :=
      abs_pos.mpr (sub_ne_zero.mpr (fun h => hlamS (h ▸ hα)))
    have h1 : 1 / |α - sepLam β eps| < 1 / |β - sepLam β eps| :=
      one_div_lt_one_div_of_lt hbpos hstrict
    have h2 : (|α - sepLam β eps|)⁻¹ < (|β - sepLam β eps|)⁻¹ := by
      simpa [one_div] using h1
    simpa [sepValue, abs_inv] using h2

/-! ## The Möbius / `P^1` form -/

/-- The explicit Möbius map `N(x) = (C eps)/(lam - x)` as the matrix
`[[0, C eps], [-1, beta + eps]]`; its determinant is `C eps != 0`. -/
def sepMoebius (C eps β : ℚ) (hC : 0 < C) (heps : 0 < eps) : MoebiusData where
  a := 0
  b := C * eps
  c := -1
  d := β + eps
  det := by
    have h : (0 : ℚ) * (β + eps) - C * eps * (-1) = C * eps := by ring
    rw [h]
    exact (mul_pos hC heps).ne'

/-- The matrix entries of `sepMoebius` (rational coefficients, as in the paper). -/
theorem sepMoebius_matrix (C eps β : ℚ) (hC : 0 < C) (heps : 0 < eps) :
    (sepMoebius C eps β hC heps).a = 0 ∧ (sepMoebius C eps β hC heps).b = C * eps ∧
      (sepMoebius C eps β hC heps).c = -1 ∧ (sepMoebius C eps β hC heps).d = β + eps :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The determinant of the explicit Möbius matrix is `C eps`. -/
theorem sepMoebius_det (C eps β : ℚ) (hC : 0 < C) (heps : 0 < eps) :
    (sepMoebius C eps β hC heps).a * (sepMoebius C eps β hC heps).d -
      (sepMoebius C eps β hC heps).b * (sepMoebius C eps β hC heps).c = C * eps := by
  obtain ⟨ha, hb, hc, hd⟩ := sepMoebius_matrix C eps β hC heps
  rw [ha, hb, hc, hd]
  ring

/-- The Möbius map agrees with `sepN` at every finite point where the denominator is
nonzero. -/
theorem sepMoebius_mapPoints_of_ne (C eps β x : ℚ) (hC : 0 < C) (heps : 0 < eps)
    (hx : β + eps - x ≠ 0) :
    (sepMoebius C eps β hC heps).mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite (sepN C eps β x) := by
  obtain ⟨ha, hb, hc, hd⟩ := sepMoebius_matrix C eps β hC heps
  have hden : (sepMoebius C eps β hC heps).c * x + (sepMoebius C eps β hC heps).d ≠ 0 := by
    rw [hc, hd]
    intro h
    exact hx (by linarith)
  rw [MoebiusData.mapPoints_finite _ hden, ha, hb, hc, hd]
  congr 1
  rw [sepN_eq_div]
  congr 1 <;> ring

/-- `N` has a pole at `lam = beta + eps`: the Möbius map sends `lam` to infinity. -/
theorem sepMoebius_mapPoints_lam (C eps β : ℚ) (hC : 0 < C) (heps : 0 < eps) :
    (sepMoebius C eps β hC heps).mapPoints (P1Point.ofFinite (sepLam β eps)) =
      P1Point.infty := by
  obtain ⟨ha, hb, hc, hd⟩ := sepMoebius_matrix C eps β hC heps
  have hpole : (sepMoebius C eps β hC heps).c * sepLam β eps +
      (sepMoebius C eps β hC heps).d = 0 := by
    rw [hc, hd]
    unfold sepLam
    ring
  exact MoebiusData.mapPoints_pole _ hpole

/-- `N(infinity) = 0`. -/
theorem sepMoebius_mapPoints_infty (C eps β : ℚ) (hC : 0 < C) (heps : 0 < eps) :
    (sepMoebius C eps β hC heps).mapPoints P1Point.infty = P1Point.ofFinite (0 : ℚ) := by
  obtain ⟨ha, hb, hc, hd⟩ := sepMoebius_matrix C eps β hC heps
  rw [MoebiusData.mapPoints_infty, hc, ha]
  simp

/-- `N(beta) = C` on `P^1`. -/
theorem sepMoebius_mapPoints_beta (C eps β : ℚ) (hC : 0 < C) (heps : 0 < eps) :
    (sepMoebius C eps β hC heps).mapPoints (P1Point.ofFinite β) =
      P1Point.ofFinite C := by
  rw [sepMoebius_mapPoints_of_ne C eps β β hC heps (by intro h; linarith),
    separation_explicit_beta C eps β heps.ne']

/-- On `S` the Möbius map is finite, with value `N(alpha)`. -/
theorem sepMoebius_mapPoints_alpha (S : Finset ℚ) (β C eps : ℚ) (hβ : β ∉ S)
    (hC : 0 < C) (heps : 0 < eps) (hbound : (C + 1) * eps ≤ sepDelta S β) :
    ∀ α ∈ S, (sepMoebius C eps β hC heps).mapPoints (P1Point.ofFinite α) =
      P1Point.ofFinite (sepN C eps β α) := by
  intro α hα
  exact sepMoebius_mapPoints_of_ne C eps β α hC heps
    ((separation_denominator_ne_zero S β C eps hβ hC heps hbound).1 α hα)

/-- On `S` the Möbius map never takes the value infinity. -/
theorem sepMoebius_mapPoints_alpha_ne_infty (S : Finset ℚ) (β C eps : ℚ)
    (hβ : β ∉ S) (hC : 0 < C) (heps : 0 < eps)
    (hbound : (C + 1) * eps ≤ sepDelta S β) :
    ∀ α ∈ S, (sepMoebius C eps β hC heps).mapPoints (P1Point.ofFinite α) ≠
      P1Point.infty := by
  intro α hα
  rw [sepMoebius_mapPoints_alpha S β C eps hβ hC heps hbound α hα]
  exact P1Point.ofFinite_ne_infty _

/-! ## Status record -/

/-- Status: the explicit rational Möbius separation of paper [Mzk1] Lemma 2.3 is PROVED,
including the `P^1`/Möbius form over `Q`.  The paper-scope `Qbar`/`C` version remains a
named statement in `Mzk1Lemma23SeparationActual`; no closure is claimed there. -/
def ExplicitSeparationStatus : Audit.Obligation :=
  { id := "MZK1.lemma23.separation-explicit"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.3 lines 163-165 (user-provided explicit Mobius proof)"
    status := Audit.VerificationStatus.provedKernel
    note := "PROVED over Q: sepDelta (min distance, 1 if empty); exists_eps_pos_le / exists_eps_le ((C+1) eps <= delta, eps = delta/(2(C+1))); sepN x = C eps/(lam - x) with lam = beta + eps; separation_explicit_beta (N beta = C); separation_explicit_alpha (|N alpha| <= 1 on S); separation_denominator_ne_zero (denominator nonzero on S and at beta); separation_lam_notin; sepLam_ne_beta; separation_strict (C > 1); sepValue bridge separation_sepValue_alpha; combined exists_explicit_separation and C = 4 specialization separation_C4; Mobius form sepMoebius with sepMoebius_mapPoints_beta / _lam (pole) / _infty / _alpha / _alpha_ne_infty. No sorry, no new axioms. Paper-scope Qbar/C statement remains named in Mzk1Lemma23SeparationActual; no closure claim."
    dependsOn := ["MZK1.lemma23.separation"] }

#check sepN
#check separation_explicit_beta
#check separation_explicit_alpha
#check separation_denominator_ne_zero
#check exists_explicit_separation
#check sepMoebius
#check sepMoebius_mapPoints_lam
#check sepMoebius_mapPoints_infty

end LeanFormal.IUT.XiFPaper.Mzk1Lemma23ExplicitActual
end
