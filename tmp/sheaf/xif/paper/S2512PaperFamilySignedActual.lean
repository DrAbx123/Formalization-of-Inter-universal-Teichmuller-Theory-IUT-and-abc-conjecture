import tmp.sheaf.xif.paper.S2510PaperFamilyCandidateActual

/-! # S2512: paper family from actual outputs under the hull bound alone

Uses exact coverage when profile(core.base) < 0 and signed coverage otherwise.
Only the hull inequality is needed; the q normalization is solved by cases. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual
open LeanFormal.IUT.XiFPaper.S2456PaperFamilyActual
open LeanFormal.IUT.XiFPaper.S2510PaperFamilyCandidateActual

namespace LeanFormal.IUT.XiFPaper.S2512PaperFamilySignedActual

universe u v ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice] [Fintype Label]
variable {X : Type ux} {P : PaperSignedHull X Label}
variable {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}

noncomputable def S2512PaperFamilySigned
    (hbound : R.input.profile.logVolume R.input.core.base ≤
      P.signedHullLogVolume) :
    S2456ActualPaperFamilyRequired P R := by
  classical
  let s := R.input.profile.logVolume R.input.core.base
  by_cases hs : s < 0
  · refine {
      P_C := Set.univ
      q := Real.exp (-s)
      q_pos := Real.exp_pos _
      q_ne_one := ?_
      nu_C := fun D => R.input.profile.logVolume D.source
      Q_C := s
      Q_C_eq_neg_abs_log_q := ?_
      readout_eq := ?_
      upper := ?_
      coverage := ?_ }
    · have hpos : 0 < -s := by linarith
      have hgt : 1 < Real.exp (-s) := Real.one_lt_exp_iff.mpr hpos
      exact ne_of_gt hgt
    · have hlog : Real.log (Real.exp (-s)) = -s := Real.log_exp _
      have hpos : 0 < -s := by linarith
      rw [hlog, abs_of_pos hpos]
      ring
    · intro D hD
      rfl
    · intro D hD
      rw [S2510_profile_const D]
      exact hbound
    · left
      exact ⟨theorem311Output R.input, Set.mem_univ _, by
        change R.input.profile.logVolume
          (theorem311Output R.input).source = s
        rw [S2510_profile_const]⟩
  · have hsnon : 0 ≤ s := le_of_not_gt hs
    refine {
      P_C := Set.univ
      q := 2
      q_pos := by norm_num
      q_ne_one := by norm_num
      nu_C := fun D => R.input.profile.logVolume D.source
      Q_C := -Real.log 2
      Q_C_eq_neg_abs_log_q := ?_
      readout_eq := ?_
      upper := ?_
      coverage := ?_ }
    · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [abs_of_pos hlog2]
    · intro D hD
      rfl
    · intro D hD
      rw [S2510_profile_const D]
      exact hbound
    · right
      intro eps heps
      refine ⟨theorem311Output R.input, Set.mem_univ _, ?_⟩
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      change -Real.log 2 - eps ≤
        R.input.profile.logVolume (theorem311Output R.input).source
      rw [S2510_profile_const]
      change -Real.log 2 - eps ≤ s
      nlinarith

#check S2512PaperFamilySigned

end LeanFormal.IUT.XiFPaper.S2512PaperFamilySignedActual
end
