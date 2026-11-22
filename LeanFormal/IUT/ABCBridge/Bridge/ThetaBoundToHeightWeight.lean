import Mathlib.Tactic

/-!
  # Theta-pilot log-volume comparison to the height-weight form (bookkeeping reduction)

  This module contains the purely real-variable reduction that turns the per-`ε`
  normalized log-volume comparison of the θ-pilot / arithmetic-line-bundle step into
  the exact height-weight shape consumed by
  `abcConjecture_iff_abcArithmeticWeightHeightBound` in
  `LeanFormal/IUT/ABCBridge/Bridge/IUTToABC.lean`.

  ## Shape

  Let `P` be a predicate on triples of naturals and let `height`, `weight` be real
  functions of the triple.  Suppose that for every `δ > 0` there is data
  `volume δ` (the `δ`-normalized log-volume of the arithmetic line bundle) with

  * `height ≤ (1 + δ) · volume δ`, and
  * `volume δ ≤ (1 + δ) · weight + thetaBound + D δ`,

  with a single real θ-pilot bound `thetaBound` and a residual per-`δ` constant
  `D δ`.  The first inequality is the paper's comparison of the height with the
  log-volume of the arithmetic line bundle in the `δ`-normalized log-shell; the
  second is the paper's `δ`-normalized log-volume computation of that line bundle,
  in which the boundedness of the θ-pilot contribution (IUT III Corollary 3.12
  supplies the corresponding finite quantity) and the finite-prime data are
  absorbed into `thetaBound + D δ`.

  Then for every `ε > 0` there is `A` with `height ≤ (1 + ε) · weight + A`: the two
  `(1 + δ)` losses are re-absorbed by taking `δ = min 1 (ε / 3)`, for which
  `(1 + δ)^2 ≤ 1 + ε`.  This re-absorption is the correction performed at the end
  of the IUT IV estimate.

  ## Honest scope

  Nothing arithmetic or geometric is proved here.  The two displayed inequality
  families are the input; everything below is real-variable bookkeeping (factor
  absorption and constant management).  This module does not prove Corollary 3.12,
  does not prove the IUT IV estimate, and does not prove ABC.
-/

namespace LeanFormal.IUT

/-- **Absorption factor.**  For every `ε > 0` there is `δ > 0` with
`(1 + δ)^2 ≤ 1 + ε`.  The witness is `δ = min 1 (ε / 3)`: if `ε / 3 ≤ 1` then
`(1 + ε/3)^2 ≤ 1 + ε`, and if `1 ≤ ε / 3` then `2^2 ≤ 1 + ε`. -/
theorem exists_oneAdd_sq_le_oneAdd (epsilon : Real) (heps : 0 < epsilon) :
    ∃ delta : Real, 0 < delta ∧ (1 + delta) ^ 2 ≤ 1 + epsilon := by
  refine ⟨min 1 (epsilon / 3), ?_, ?_⟩
  · exact lt_min one_pos (by linarith)
  · rcases le_total (epsilon / 3) 1 with hle | hle
    · rw [min_eq_right hle]
      have h1 : 0 ≤ epsilon / 3 := by linarith
      have h2 : (epsilon / 3) * (epsilon / 3) ≤ 1 * (epsilon / 3) :=
        mul_le_mul_of_nonneg_right hle h1
      nlinarith [h2]
    · rw [min_eq_left hle]
      nlinarith

/-- **θ-pilot-bound-to-height-weight reduction.**  From a `δ`-indexed family of
normalized log-volume comparisons with a single real θ-pilot bound `thetaBound`
(the shape displayed in the module header), derive the height-weight bound
`height ≤ (1 + ε) · weight + A` for every `ε > 0`, with `A` depending only on `ε`
and on the comparison data.  No arithmetic content is assumed beyond the two
inequality families; the proof is the factor absorption of
`exists_oneAdd_sq_le_oneAdd`. -/
theorem heightWeightBound_of_normalizedVolumeComparison
    {P : Nat → Nat → Nat → Prop} (height weight : Nat → Nat → Nat → Real)
    (volume : ∀ (delta : Real), 0 < delta → Nat → Nat → Nat → Real)
    (thetaBound : Real)
    (hweight_nonneg : ∀ a b c, P a b c → 0 ≤ weight a b c)
    (hcomparison : ∀ (delta : Real) (hdelta : 0 < delta),
      (∀ a b c, P a b c → height a b c ≤ (1 + delta) * volume delta hdelta a b c) ∧
      ∃ D : Real, ∀ a b c, P a b c →
        volume delta hdelta a b c ≤ (1 + delta) * weight a b c + thetaBound + D) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c, P a b c →
      height a b c ≤ (1 + epsilon) * weight a b c + A := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta_pos, hdelta_sq⟩ := exists_oneAdd_sq_le_oneAdd epsilon hepsilon
  obtain ⟨D, hD⟩ := (hcomparison delta hdelta_pos).2
  refine ⟨(1 + delta) * (thetaBound + D), ?_⟩
  intro a b c habc
  have hheight := (hcomparison delta hdelta_pos).1 a b c habc
  have hvol := hD a b c habc
  have hweight := hweight_nonneg a b c habc
  have hscaled : (1 + delta) * volume delta hdelta_pos a b c ≤
      (1 + delta) * ((1 + delta) * weight a b c + thetaBound + D) :=
    mul_le_mul_of_nonneg_left hvol (by linarith)
  have hexpand : (1 + delta) * ((1 + delta) * weight a b c + thetaBound + D) =
      (1 + delta) ^ 2 * weight a b c + (1 + delta) * (thetaBound + D) := by
    ring
  rw [hexpand] at hscaled
  have hsquare : (1 + delta) ^ 2 * weight a b c ≤ (1 + epsilon) * weight a b c :=
    mul_le_mul_of_nonneg_right hdelta_sq hweight
  linarith

end LeanFormal.IUT
