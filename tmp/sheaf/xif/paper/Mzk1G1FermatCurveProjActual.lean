import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveProjActual
/-- Projective Fermat curve `X^n+Y^n=Z^n` as a subset of coordinates. -/
def projFermatCurve (n : Nat) : Set (Fin 3 → ℚ) :=
  {p | p 0 ^ n + p 1 ^ n = p 2 ^ n ∧ p ≠ 0}
/-- The projective base point `[1:0:1]`. -/
def projFermatBase : Fin 3 → ℚ :=
  ![1, 0, 1]
theorem projFermatBase_mem (hn : 0 < n) :
    projFermatBase ∈ projFermatCurve n := by
  constructor
  · simp [projFermatBase, zero_pow (Nat.pos_iff_ne_zero.mp hn)]
  · intro h
    have h0 := congrFun h 0
    simp [projFermatBase] at h0
theorem projFermatCurve_nonempty (hn : 0 < n) :
    (projFermatCurve n).Nonempty := ⟨projFermatBase, projFermatBase_mem hn⟩
#print axioms projFermatBase_mem
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveProjActual
end