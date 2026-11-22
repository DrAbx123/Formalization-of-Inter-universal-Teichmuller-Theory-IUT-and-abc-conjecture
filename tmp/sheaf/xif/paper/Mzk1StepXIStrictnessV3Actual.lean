import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi 1D and product strictness

Pure order lemmas used by the strict_measure/annulus lane: one-dimensional strict
conversion to ENNReal and finite-product strict increase for nonnegative factors. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessV3Actual

theorem oneDim_ennreal_strict {a b : Real} (ha : 0 < a) (h : a < b) :
    ENNReal.ofReal a < ENNReal.ofReal b :=
  (ENNReal.ofReal_lt_ofReal_iff (lt_trans ha h)).mpr h

theorem product_strict {α : Type*} [Fintype α] (f g : α → Real)
    (hf : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) :
    (∏ i, f i) < ∏ i, g i := by
  obtain ⟨i, hi⟩ := hlt
  simpa using (Finset.prod_lt_prod (s := Finset.univ) (fun j _ => hf j)
    (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩)

theorem product_strict_of_one (α : Type*) [Fintype α] [Nonempty α]
    (f g : α → Real) (i : α) (hf : ∀ j, 0 < f j) (hle : ∀ j, f j ≤ g j)
    (hi : f i < g i) :
    (∏ j, f j) < ∏ j, g j :=
  product_strict f g hf hle ⟨i, hi⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessV3Actual

end
