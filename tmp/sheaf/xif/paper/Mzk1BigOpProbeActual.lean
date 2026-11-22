/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! A1033: diagnostic probe: which big-operators sum syntax is available in our pin. -/

noncomputable section
open scoped BigOperators
open Finset

#check (∑ j in Finset.range 5, ((j + 1 : Real) ^ 2))
#check (∑ j ∈ Finset.range 5, ((j + 1 : Real) ^ 2))

theorem probe_sum_notation (n : Nat) :
    (∑ j in Finset.range n, ((j : Real) + 1)) = (∑ j ∈ Finset.range n, ((j : Real) + 1)) := rfl

end
