import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Mzk1StrictMeasureInstanceActual — strict_measure instantiation (non-vacuity witness)

A547 module: a concrete MODEL instance of the non-vacuous xi-e requirement on the toy
carrier `Real`, with an explicitly defined monotone volume functional, used to
instantiate the `strict_measure` field and exercise the Cor 3.12 assembly.  This is a
non-vacuity witness for the gate, NOT a model of the paper carrier.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureInstanceActual

open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

/-- Toy volume functional on subsets of `Real`: 2 for regions containing both 0 and 1,
1 for other nonempty regions, 0 for the empty region. -/
noncomputable def toyVol (S : Set Real) : Real :=
  letI := Classical.propDecidable
  if (0 : Real) ∈ S ∧ (1 : Real) ∈ S then 2 else if S.Nonempty then 1 else 0

/-- Value on the empty region. -/
theorem toyVol_empty : toyVol ∅ = 0 := by
  unfold toyVol
  simp

/-- Value on the singleton {0}. -/
theorem toyVol_singleton_zero : toyVol {(0 : Real)} = 1 := by
  unfold toyVol
  rw [if_neg (by norm_num), if_pos]
  · norm_num
  · exact ⟨0, rfl⟩

/-- Value on the pair {0,1}. -/
theorem toyVol_pair : toyVol ({(0 : Real), 1}) = 2 := by
  unfold toyVol
  rw [if_pos]
  · norm_num
  · exact ⟨by norm_num, by norm_num⟩

/-- The toy volume is monotone under inclusion. -/
theorem toyVol_mono {S T : Set Real} (h : S ⊆ T) : toyVol S <= toyVol T := by
  unfold toyVol
  by_cases hS : (0 : Real) ∈ S ∧ (1 : Real) ∈ S
  · rw [if_pos hS]
    have hT : (0 : Real) ∈ T ∧ (1 : Real) ∈ T := ⟨h hS.1, h hS.2⟩
    rw [if_pos hT]
    norm_num
  · rw [if_neg hS]
    by_cases hT : (0 : Real) ∈ T ∧ (1 : Real) ∈ T
    · rw [if_pos hT]; norm_num
    · rw [if_neg hT]
      by_cases hne : S.Nonempty
      · rw [if_pos hne]
        have hneT : T.Nonempty := hne.mono h
        rw [if_pos hneT]
      · rw [if_neg hne, if_neg]; norm_num
        intro hTne
        exact hne (hTne.mono (Set.subset.refl S)) |>.elim

/-- The model xi-e requirement on `Real`: q-region = {0}, possible images = {0},
hull = {0,1}; strict measure 1 < 2. -/
noncomputable def toyRequirement : XiEContainmentRequirement Real toyVol where
  qRegion := {0}
  thetaPossibleImages := {0}
  hullRegion := {0, 1}
  q_in_possible := by intro x hx; exact hx
  possible_in_hull := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  q_pos := by
    rw [toyVol_singleton_zero]
    norm_num
  strict_measure := by
    rw [toyVol_singleton_zero, toyVol_pair]
    norm_num

/-- The model requirement gives the strict signed comparison (non-vacuity of Cor 3.12). -/
theorem toy_strict_signed :
    requirementSignedQ toyRequirement < requirementSignedTheta toyRequirement :=
  requirement_strict_signed toyRequirement

/-- The model requirement gives the Cor 3.12 conclusion. -/
theorem toy_cor312 :
    Cor312Conclusion (requirementContract toyRequirement
      (by unfold requirementSignedQ signedLogVolume toyRequirement;
          rw [show toyVol {0} = 1 from by
            unfold toyVol
            rw [if_neg (by norm_num), if_pos]
            · rfl
            · exact ⟨0, rfl⟩]
          norm_num)
      (True) trivial (True) trivial (True) trivial) :=
  requirement_cor312 toyRequirement
    (by unfold requirementSignedQ signedLogVolume toyRequirement;
        rw [show toyVol {0} = 1 from by
          unfold toyVol
          rw [if_neg (by norm_num), if_pos]
          · rfl
          · exact ⟨0, rfl⟩]
        norm_num)
    (True) trivial (True) trivial (True) trivial

#check toyVol
#check toyVol_mono
#check toyRequirement
#check toy_strict_signed
#check toy_cor312

end LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureInstanceActual
end
