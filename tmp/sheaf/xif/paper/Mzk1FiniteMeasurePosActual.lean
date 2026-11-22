import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteMeasurePosActual — positivity/nonemptiness for the finite measure (real)

Real Lean (no sorry/axiom): maximal degree is positive exactly for nonempty finite sets;
useful for the base case of the finite nested induction.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasurePosActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_pos_iff_nonempty (S : Finset Qbar) : 0 < maxDeg S <-> S.Nonempty := by
  constructor
  · intro h
    by_contra hne
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at h
    unfold maxDeg at h
    simp at h
  · intro hne
    obtain ⟨x, hx⟩ := hne
    have hle : degQ x <= maxDeg S := by
      unfold maxDeg
      exact Finset.le_sup hx
    exact lt_of_lt_of_le (degQ_pos x) hle

theorem maxDeg_eq_zero_iff_not_nonempty (S : Finset Qbar) :
    maxDeg S = 0 <-> ¬ S.Nonempty := by
  constructor
  · intro h hne
    have hpos := (maxDeg_pos_iff_nonempty S).mpr hne
    omega
  · intro hne
    have hnot : ¬ 0 < maxDeg S := by
      intro hpos
      exact hne ((maxDeg_pos_iff_nonempty S).mp hpos)
    omega

def finiteMeasurePosRows : List (String × String) :=
  [ ("maxDeg_pos_iff_nonempty", "PROVED"), ("maxDeg_eq_zero_iff_not_nonempty", "PROVED") ]

theorem finiteMeasurePosRows_length : finiteMeasurePosRows.length = 2 := rfl

#check maxDeg_pos_iff_nonempty

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasurePosActual
end
