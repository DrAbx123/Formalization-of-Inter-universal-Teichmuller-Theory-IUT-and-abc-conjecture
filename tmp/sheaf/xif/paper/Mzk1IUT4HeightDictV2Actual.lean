import Mathlib

/-!
# Mzk1IUT4HeightDictV2Actual — height dictionary comparison (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Pointwise height comparison relation is transitive; composition of comparisons (genuine). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUT4HeightDictV2Actual

/-- Height comparison: pointwise height ≤ comparison function. -/
def HeightLe {X : Type*} (h v : X → ℚ) : Prop := ∀ x, h x ≤ v x

/-- Genuine theorem: height comparison is transitive. -/
theorem HeightLe.trans {X : Type*} {h v w : X → ℚ}
    (h1 : HeightLe h v) (h2 : HeightLe v w) : HeightLe h w :=
  fun x => le_trans (h1 x) (h2 x)

/-- Genuine theorem: height comparison is reflexive. -/
theorem HeightLe.refl {X : Type*} (h : X → ℚ) : HeightLe h h :=
  fun _ => le_rfl

/-- Genuine theorem: adding a common function preserves height comparison. -/
theorem HeightLe.add_right {X : Type*} {h v : X → ℚ} (hv : HeightLe h v)
    (w : X → ℚ) : HeightLe (fun x => h x + w x) (fun x => v x + w x) :=
  fun x => add_le_add_right (hv x) (w x)

end LeanFormal.IUT.XiFPaper.Mzk1IUT4HeightDictV2Actual
