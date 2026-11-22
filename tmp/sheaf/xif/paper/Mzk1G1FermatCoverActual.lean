import Mathlib

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual

universe u
variable (k : Type u) [Field k] (n : ℕ)

/-- Actual affine Fermat curve X^n + Y^n = 1. -/
def FermatCurve : Type u := {p : k × k // p.1 ^ n + p.2 ^ n = 1}

/-- The base point (0,1) for n>0. -/
def fermatBasePoint (hn : 0 < n) : FermatCurve k n :=
  ⟨(0, 1), by simp [FermatCurve, zero_pow (Nat.pos_iff_ne_zero.mp hn)]⟩

/-- Actual Fermat cover data. -/
structure FermatCoverData where
  n : ℕ
  hn : 0 < n
  curve : Type u
  coverMap : curve → k
  basePoint : curve

/-- The actual Fermat cover attached to n>0. -/
def fermatCoverData (hn : 0 < n) : FermatCoverData k where
  n := n
  hn := hn
  curve := FermatCurve k n
  coverMap := fun p => p.1.1
  basePoint := fermatBasePoint k n hn

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
