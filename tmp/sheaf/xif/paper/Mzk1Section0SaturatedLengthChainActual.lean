/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedSetsActual

/-! # Section 0 chain: constant-length path-pair sets are saturated -/

namespace LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual

variable {V E : Type*}

/-- Sets of path pairs of a fixed total length are saturated under every
vertex map (the length is invariant under endpoint maps). -/
theorem saturated_lengthSet (G : V → V → Prop) (n : Nat) :
    Saturated G {p : PathPair V E | pairLength p = n} := by
  intro sigma h p
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, pairLength_map]

theorem saturated_lengthSet_le (G : V → V → Prop) (n : Nat) :
    Saturated G {p : PathPair V E | pairLength p ≤ n} := by
  intro sigma h p
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, pairLength_map]

end LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual
