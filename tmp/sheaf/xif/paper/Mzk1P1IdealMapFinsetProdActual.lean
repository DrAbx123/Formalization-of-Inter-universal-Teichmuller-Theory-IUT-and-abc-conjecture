/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-! # P1: Ideal.map is multiplicative on finite products -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinsetProdActual

variable {R S : Type} [CommRing R] [CommRing S]
variable {β : Type} (f : R →+* S)

/-- `Ideal.map` commutes with finite products of ideals. -/
theorem ideal_map_finset_prod (s : Finset β) (g : β → Ideal R) :
    Ideal.map f (∏ i ∈ s, g i) = ∏ i ∈ s, Ideal.map f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]

/-- Multiplicative version with a single Finset.prod binder. -/
theorem ideal_map_finset_prod' (s : Finset β) (g : β → Ideal R) :
    Ideal.map f (s.prod g) = s.prod (fun i => Ideal.map f (g i)) :=
  ideal_map_finset_prod (f := f) s g

def finsetProdRows : List (String × String × String) :=
  [ ("ideal_map_finset_prod", "Ideal.map f (prod g) = prod (map f ∘ g)", "PROVED"),
    ("ideal_map_finset_prod'", "single Finset.prod form", "PROVED") ]

theorem finsetProdRows_length : finsetProdRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinsetProdActual

end