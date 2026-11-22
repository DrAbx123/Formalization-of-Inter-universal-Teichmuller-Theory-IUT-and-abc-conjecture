import Mathlib

/-!
# Mzk1KummerComposeChainActual — chained Kummer/injectivity consequences (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers combining injectivity/section theorems (Mathlib) into new consequences. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerComposeChainActual

/-- Chained: composition of injective maps is injective. -/
theorem injective_comp_chain {S T U : Type*} {f : S → T} {g : T → U}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  hg.comp hf

/-- Chained: a left inverse certifies injectivity. -/
theorem injective_of_leftInverse_chain {S T : Type*} {f : S → T} {sec : T → S}
    (h : ∀ x, sec (f x) = x) : Function.Injective f := by
  intro x y hxy
  have hx := h x
  have hy := h y
  rw [hxy] at hx
  exact hx.symm.trans hy

/-- Chained: injectivity preserved under post-composition with an injective map. -/
theorem injective_postcomp_chain {S T U : Type*} {f : S → T} {h : T → U}
    (hf : Function.Injective f) (hh : Function.Injective h) :
    Function.Injective (fun x => h (f x)) :=
  hh.comp hf

end LeanFormal.IUT.XiFPaper.Mzk1KummerComposeChainActual
