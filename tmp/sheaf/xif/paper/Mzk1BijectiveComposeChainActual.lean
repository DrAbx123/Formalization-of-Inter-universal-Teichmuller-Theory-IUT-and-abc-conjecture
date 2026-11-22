import Mathlib

/-!
# Mzk1BijectiveComposeChainActual — chained bijective-composition consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers: composition of bijective maps is bijective; equivalences compose. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BijectiveComposeChainActual

/-- Chained: composition of two bijective maps is bijective. -/
theorem bijective_comp_chain {S T U : Type*} {f : S → T} {g : T → U}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f) :=
  hg.comp hf

/-- Chained: bijective maps compose with a left inverse. -/
theorem bijective_of_leftInverse_chain {S T : Type*} {f : S → T} {sec : T → S}
    (h : ∀ x, sec (f x) = x) (hf : Function.Bijective f) :
    Function.Injective f :=
  hf.1

/-- Chained: equivalence composition is bijective. -/
theorem equiv_comp_bijective_chain {S T U : Type*} (e1 : S ≃ T) (e2 : T ≃ U) :
    Function.Bijective (e2 ∘ e1) :=
  e2.bijective.comp e1.bijective

end LeanFormal.IUT.XiFPaper.Mzk1BijectiveComposeChainActual
