/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: finite-cardinality arithmetic for prime sets -/

namespace LeanFormal.IUT.XiFPaper.FinsetCardArithmeticActual

variable {α : Type*} [DecidableEq α]

theorem card_union_disjoint' {s t : Finset α} (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card := Finset.card_union_of_disjoint h

theorem card_inter_le_left' (s t : Finset α) : (s ∩ t).card ≤ s.card := 
  Finset.card_inter_le s t

theorem card_sdiff_of_subset {s t : Finset α} (h : t ⊆ s) :
    (s \ t).card = s.card - t.card := Finset.card_sdiff h

theorem card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  Finset.card_union_le s t

theorem card_insert_of_notMem {s : Finset α} {a : α} (h : a ∉ s) :
    (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem h

end LeanFormal.IUT.XiFPaper.FinsetCardArithmeticActual
