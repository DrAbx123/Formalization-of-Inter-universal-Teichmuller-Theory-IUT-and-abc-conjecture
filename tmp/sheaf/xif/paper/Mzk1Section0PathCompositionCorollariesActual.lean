/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Section0PathCompositionActual

/-! # Reuse: corollaries of the Section-0 path-composition addendum -/

namespace LeanFormal.IUT.XiFPaper.Section0PathCompositionActual

variable {V E : Type*}

theorem pdLength_append_three (p q r : PathData V E)
    (h1 : p.end_ = q.start) (h2 : q.end_ = r.start) :
    pdLength (pdAppend (pdAppend p q h1) r h2) =
      pdLength p + pdLength q + pdLength r := by
  rw [pdAppend_length, pdAppend_length]
  ring

theorem pdReverse_length_twice (p : PathData V E) :
    pdLength (pdReverse (pdReverse p)) = pdLength p := by
  rw [pdReverse_length, pdReverse_length]

theorem pdLength_append_nil' (p : PathData V E) :
    pdLength (pdAppend p (pdNil (E := E) p.end_) rfl) = pdLength p := by
  rw [pdAppend_length, pdNil_length]
  exact Nat.add_zero (pdLength p)

theorem pdLength_nil_append' (p : PathData V E) :
    pdLength (pdAppend (pdNil (E := E) p.start) p rfl) = pdLength p := by
  rw [pdAppend_length, pdNil_length]
  exact Nat.zero_add (pdLength p)

end LeanFormal.IUT.XiFPaper.Section0PathCompositionActual
