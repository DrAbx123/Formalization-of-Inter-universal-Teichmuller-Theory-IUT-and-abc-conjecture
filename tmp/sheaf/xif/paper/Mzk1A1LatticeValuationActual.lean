import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Field.Defs
/-! #A1.5/A1.6 generic valuation form of the inverse lattice (natural orders).

For nonnegative integer orders `a : F -> Nat`, `b : L -> Nat` with ramification
`b (iota x) = e * a x`, the inverse image of the principal lattice
`{y | m <= b y}` is the saturated lattice `{x | ceilDiv m e <= a x}`.
This is the exact lattice part of `J_s = pi_F^(ceil(m/e)) O_F`; the
ramification identity and the signed readout are recorded as the remaining
instantiations, not assumed as comparison hypotheses. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationActual
variable {F L : Type*} [Field F] [Field L]
/-- Nonnegative principal lattice `{y | m <= b y}`. -/
def principalLattice (b : L -> Nat) (m : Nat) : Set L := {y | m <= b y}
/-- Inverse image lattice under `iota : F -> L`. -/
def inverseLattice (iota : F -> L) (b : L -> Nat) (m : Nat) : Set F :=
  {x | iota x ∈ principalLattice b m}
/-- Saturated lattice `{x | ceilDiv m e <= a x}`. -/
def saturatedLattice (a : F -> Nat) (m : Nat) (e : Nat) : Set F :=
  {x | m ⌈/⌉ e <= a x}
/-- Under the ramification identity and `b lam = m`, the inverse lattice is
exactly the saturated lattice. -/
theorem inverseLattice_eq_saturated
    (iota : F -> L) (a : F -> Nat) (b : L -> Nat)
    (e : Nat) (he : 0 < e) (m : Nat)
    (hram : ∀ x : F, b (iota x) = e * a x) :
    inverseLattice iota b m = saturatedLattice a m e := by
  ext x
  simp only [inverseLattice, principalLattice, saturatedLattice, Set.mem_setOf_eq]
  rw [hram x]
  have hceil := (ceilDiv_le_iff_le_smul (a := e) (b := m) (c := a x) he).symm
  simpa [smul_eq_mul] using hceil
/-- The actual q element lies in the inverse lattice when its image has the
same order as `lam`. -/
theorem q_mem_inverseLattice
    (iota : F -> L) (b : L -> Nat) (m : Nat) (q : F)
    (hq : b (iota q) = m) : q ∈ inverseLattice iota b m := by
  simpa [inverseLattice, principalLattice] using hq.ge
end LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationActual
end