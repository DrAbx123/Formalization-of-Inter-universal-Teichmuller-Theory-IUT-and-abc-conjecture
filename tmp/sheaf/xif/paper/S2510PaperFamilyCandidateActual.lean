import tmp.sheaf.xif.paper.S2456PaperFamilyActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import tmp.sheaf.n8.closure.C9IUTBridgeOutput

/-! # S2510: conditional paper-family candidate from the actual outputs

Every actual output has source = the core base, so the profile readout is
constant on ActualOutput.  If that value is negative and bounded by the paper
signed hull, the full S2456 family can be filled with P_C = all actual outputs,
nu_C = profile readout, Q_C = profile(base), and q adjusted by exp.  The two
inequalities are the exact remaining paper-side inputs; no fake q/P is chosen. -/

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

namespace LeanFormal.IUT.XiFPaper.S2510PaperFamilyCandidateActual

universe u v w ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice] [Fintype Label]
variable {X : Type ux} {P : PaperSignedHull X Label}
variable {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}

theorem S2510_profile_const (D : ActualOutput R) :
    R.input.profile.logVolume D.source =
      R.input.profile.logVolume R.input.core.base := by
  rw [D.source_eq]

theorem S2510_packet_profile_const (D : ActualOutput R) :
    R.packet.logVolume D.source = R.packet.logVolume R.procession.base := by
  rw [D.source_eq]
  rfl

noncomputable def S2510PaperFamilyCandidate
    (hs : R.input.profile.logVolume R.input.core.base < 0)
    (hbound : R.input.profile.logVolume R.input.core.base ≤
      P.signedHullLogVolume) :
    S2456ActualPaperFamilyRequired P R where
  P_C := Set.univ
  q := Real.exp (-(R.input.profile.logVolume R.input.core.base))
  q_pos := Real.exp_pos _
  q_ne_one := by
    have hpos : 0 < -(R.input.profile.logVolume R.input.core.base) := by linarith
    have hgt : 1 < Real.exp (-(R.input.profile.logVolume R.input.core.base)) :=
      Real.one_lt_exp_iff.mpr hpos
    exact ne_of_gt hgt
  nu_C := fun D => R.input.profile.logVolume D.source
  Q_C := R.input.profile.logVolume R.input.core.base
  Q_C_eq_neg_abs_log_q := by
    have hlog : Real.log (Real.exp (-(R.input.profile.logVolume R.input.core.base)))
        = -(R.input.profile.logVolume R.input.core.base) := Real.log_exp _
    have hpos : 0 < -(R.input.profile.logVolume R.input.core.base) := by linarith
    rw [hlog, abs_of_pos hpos]
    ring
  readout_eq := by
    intro D hD
    rfl
  upper := by
    intro D hD
    rw [S2510_profile_const D]
    exact hbound
  coverage := by
    left
    exact ⟨theorem311Output R.input, Set.mem_univ _, by
      simp [S2510_packet_profile_const]⟩

#check S2510PaperFamilyCandidate
#check S2510_profile_const

end LeanFormal.IUT.XiFPaper.S2510PaperFamilyCandidateActual
end
