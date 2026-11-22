/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1AbsoluteKummerTrioSummaryActual

/-! # Reuse: consumer facts for the Absolute Kummer trio row index -/

namespace LeanFormal.IUT.XiFPaper.AbsoluteKummerTrioSummaryActual

theorem absoluteKummerTrioRows_length' : absoluteKummerTrioRows.length = 10 :=
  absoluteKummerTrioRows_length

theorem absoluteKummerTrioRows_nonempty : absoluteKummerTrioRows ≠ [] := by
  intro h
  have hlen := absoluteKummerTrioRows_length
  rw [h] at hlen
  simp at hlen

theorem absoluteKummerTrioRows_head : ∃ x, absoluteKummerTrioRows.head? = some x := by
  cases h : absoluteKummerTrioRows with
  | nil =>
      exfalso
      have hlen := absoluteKummerTrioRows_length
      rw [h] at hlen
      simp at hlen
  | cons x xs =>
      exact ⟨x, rfl⟩

theorem absoluteKummerTrioRows_length_pos : 0 < absoluteKummerTrioRows.length :=
  by rw [absoluteKummerTrioRows_length]; norm_num

end LeanFormal.IUT.XiFPaper.AbsoluteKummerTrioSummaryActual
