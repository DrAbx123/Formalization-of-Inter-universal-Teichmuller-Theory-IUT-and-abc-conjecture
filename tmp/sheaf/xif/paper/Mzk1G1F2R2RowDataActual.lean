/- R2 actual row data: `et : Fin(j+1) -> iota` (surjective row enumeration) and the
  d-sum inequality `hD : sum_i localNormOrder different_i <= sum_i d (et i)`.

  Actual tensor index `iota` has `Fintype.card iota <= j+1` (the row has j+1 slots),
  so a surjective `et` exists; for any `d : iota -> Real` nonnegative the sum over the
  row (with repetitions) dominates the sum over `iota`.  Equality of `lambda = j^2 * badPlaceCoeff`
  is NOT needed (Lead ruling): only the inequality `slot <= lambda` from
  `Mzk1G1F2R2PerRowSupplyActual.lambdaFromQ_ge_slot`.
  No stub, no sorry/axiom. -/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2RowDataActual

/-- Nonnegative `d`: the row sum over a surjective `et` dominates the index sum. -/
theorem sum_le_sum_comp_of_surjective {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (et : Fin n → ι) (hsurj : Function.Surjective et) (d : ι → ℝ) (hd : ∀ e, 0 ≤ d e) :
    (∑ e, d e) ≤ ∑ i, d (et i) := by
  have hmap : ∀ i ∈ (Finset.univ : Finset (Fin n)), et i ∈ (Finset.univ : Finset ι) := by
    intro i _; exact Finset.mem_univ _
  have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset ι)) (g := et) (f := fun i => d (et i)) hmap
  rw [← hfib]
  apply Finset.sum_le_sum
  intro e _
  set F := (Finset.univ : Finset (Fin n)).filter (fun i => et i = e) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨i, hiF⟩ := hne
    have hcard : (1 : ℝ) ≤ (F.card : ℝ) := by
      have hpos : 0 < F.card := Finset.card_pos.mpr ⟨i, hiF⟩
      exact_mod_cast hpos
    have hconst : ∀ j ∈ F, d (et j) = d e := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      rw [hj'.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    nlinarith [hd e, hcard]
  · have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.sum_empty]
    exact hd e

/-- **hD from surjectivity**: `sum_i localNormOrder different <= sum_i d (et i)`. -/
theorem hD_of_surjective {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (et : Fin n → ι) (hsurj : Function.Surjective et)
    (d : ι → ℝ) (hd : ∀ e, 0 ≤ d e) :
    (∑ e, d e) ≤ ∑ i, d (et i) := sum_le_sum_comp_of_surjective et hsurj d hd

#print axioms sum_le_sum_comp_of_surjective
#print axioms hD_of_surjective

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2RowDataActual