import Mathlib

/-!
# Mzk1LogShellInvariantActionV2Actual — invariant sets of monoid actions (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Fixed-point sets under MulAction: unit action, product closure, inverse closure. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellInvariantActionV2Actual

/-- Points fixed by a monoid element under a MulAction. -/
def fixedBy (M X : Type*) [Monoid M] [MulAction M X] (m : M) : Set X :=
  { x | m • x = x }

/-- Genuine theorem: the unit acts trivially, so every point is fixed. -/
theorem fixedBy_one (M X : Type*) [Monoid M] [MulAction M X] :
    fixedBy M X (1 : M) = Set.univ := by
  ext x
  simp [fixedBy]

/-- Genuine theorem: a point fixed by m and n is fixed by their product. -/
theorem fixedBy_mul_mem (M X : Type*) [Monoid M] [MulAction M X]
    {m n : M} {x : X} (hm : x ∈ fixedBy M X m) (hn : x ∈ fixedBy M X n) :
    x ∈ fixedBy M X (m * n) := by
  change (m * n) • x = x
  change n • x = x at hn
  change m • x = x at hm
  rw [mul_smul, hn, hm]

/-- Genuine theorem: fixedness of inverses (in a group action). -/
theorem fixedBy_inv_mem (M X : Type*) [Group M] [MulAction M X]
    {m : M} {x : X} (hm : x ∈ fixedBy M X m) : x ∈ fixedBy M X m⁻¹ := by
  change m⁻¹ • x = x
  change m • x = x at hm
  calc m⁻¹ • x = m⁻¹ • (m • x) := by rw [hm]
    _ = x := inv_smul_smul m x

end LeanFormal.IUT.XiFPaper.Mzk1LogShellInvariantActionV2Actual
