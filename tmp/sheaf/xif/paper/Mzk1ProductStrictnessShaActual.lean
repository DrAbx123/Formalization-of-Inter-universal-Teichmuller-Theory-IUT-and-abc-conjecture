import Mathlib

/-!
# A579 product strictness tools (shehdd, for hull's product-wise strictness)

Wraps Mathlib's `Finset.prod_lt_prod` for the real line: positive factors,
pointwise `f <= g`, and one strict factor imply strict product inequality.
Also supplies the `Finset.univ` form.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ProductStrictnessShaActual

theorem finset_prod_lt_prod_real {ι : Type*} (s : Finset ι) {f g : ι → Real}
    (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    (∏ i ∈ s, f i) < ∏ i ∈ s, g i :=
  Finset.prod_lt_prod hf hfg hlt

theorem prod_univ_lt_prod_univ_real {ι : Type*} [Fintype ι]
    {f g : ι → Real} (hf : ∀ i, 0 < f i) (hfg : ∀ i, f i ≤ g i)
    (hlt : ∃ i, f i < g i) :
    (∏ i, f i) < ∏ i, g i := by
  simpa using finset_prod_lt_prod_real (Finset.univ : Finset ι)
    (fun i _ => hf i) (fun i _ => hfg i)
    (by rcases hlt with ⟨i, hi⟩; exact ⟨i, Finset.mem_univ i, hi⟩)

/-- Ratio form: a product of ratios with one entry `> 1` exceeds `1` when all
factors are positive and all ratios are `>= 1`. -/
theorem one_lt_prod_univ_ratio {ι : Type*} [Fintype ι]
    {f g : ι → Real} (hf : ∀ i, 0 < f i) (hfg : ∀ i, f i ≤ g i)
    (hlt : ∃ i, f i < g i) : 1 < (∏ i, g i) / (∏ i, f i) := by
  have hprod : (∏ i, f i) < ∏ i, g i := prod_univ_lt_prod_univ_real hf hfg hlt
  have hpos : 0 < ∏ i, f i := Finset.prod_pos (fun i _ => hf i)
  rw [lt_div_iff₀ hpos]
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1ProductStrictnessShaActual
