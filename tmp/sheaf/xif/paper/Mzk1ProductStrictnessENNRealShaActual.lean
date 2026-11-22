import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real

/-!
# A587 ENNReal product strictness: witness / toReal transfer (shehdd)

For hull's product-wise strictness (`prod_lt_prod` witness then taking `.toReal`):
* `prod_toReal_lt_prod_toReal`: ENNReal strict product inequality transfers to
  the product of `.toReal`s when all factors are finite;
* `prod_toReal_lt_iff`: the exact iff for finite factors;
* `prod_lt_prod_witness`: witness-based strict product inequality for a
  linearly ordered field (real line), useful when the witness is supplied by a
  single strictly increasing coordinate.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ProductStrictnessENNRealShaActual

open scoped BigOperators ENNReal

theorem prod_toReal_lt_prod_toReal {ι : Type*} [Fintype ι]
    {f g : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ⊤) (hg : ∀ i, g i ≠ ⊤)
    (h : (∏ i, f i) < ∏ i, g i) :
    (∏ i, (f i).toReal) < ∏ i, (g i).toReal := by
  rw [← ENNReal.toReal_prod, ← ENNReal.toReal_prod]
  exact (ENNReal.toReal_lt_toReal (ENNReal.prod_ne_top (fun i _ => hf i))
    (ENNReal.prod_ne_top (fun i _ => hg i))).mpr h

theorem prod_toReal_lt_iff {ι : Type*} [Fintype ι]
    {f g : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ⊤) (hg : ∀ i, g i ≠ ⊤) :
    (∏ i, (f i).toReal) < ∏ i, (g i).toReal ↔
      (∏ i, f i) < ∏ i, g i := by
  rw [← ENNReal.toReal_prod, ← ENNReal.toReal_prod]
  exact ENNReal.toReal_lt_toReal (ENNReal.prod_ne_top (fun i _ => hf i))
    (ENNReal.prod_ne_top (fun i _ => hg i))

/-- Real-line strict product inequality from explicit positive factors and a
strict witness. -/
theorem prod_lt_prod_witness {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (hlt : f i₀ < g i₀) :
    (∏ i ∈ s, f i) < ∏ i ∈ s, g i :=
  Finset.prod_lt_prod hf hfg ⟨i₀, hi₀, hlt⟩

end LeanFormal.IUT.XiFPaper.Mzk1ProductStrictnessENNRealShaActual
