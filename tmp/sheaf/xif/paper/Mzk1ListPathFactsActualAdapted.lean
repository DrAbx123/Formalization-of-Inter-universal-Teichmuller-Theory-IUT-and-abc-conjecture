/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: list-path arithmetic for edge sequences -/

namespace LeanFormal.IUT.XiFPaper.ListPathFactsActual

variable {α : Type*}

theorem length_append' (l1 l2 : List α) :
    (l1 ++ l2).length = l1.length + l2.length := List.length_append l1 l2

theorem length_reverse' (l : List α) : l.reverse.length = l.length := List.length_reverse l

theorem reverse_reverse' (l : List α) : l.reverse.reverse = l := List.reverse_reverse l

theorem append_nil' (l : List α) : l ++ [] = l := List.append_nil l

theorem nil_append' (l : List α) : [] ++ l = l := List.nil_append l

theorem append_assoc' (l1 l2 l3 : List α) :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := List.append_assoc l1 l2 l3

theorem length_append_three (l1 l2 l3 : List α) :
    (l1 ++ l2 ++ l3).length = l1.length + l2.length + l3.length := by
  simp [List.length_append]
  ring

end LeanFormal.IUT.XiFPaper.ListPathFactsActual
