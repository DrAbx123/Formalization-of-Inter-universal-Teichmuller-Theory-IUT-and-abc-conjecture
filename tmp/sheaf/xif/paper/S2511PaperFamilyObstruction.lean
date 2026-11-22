import tmp.sheaf.xif.paper.S2510PaperFamilyCandidateActual

/-! # S2511: hull obstruction for any paper family with the actual profile

Every actual output has profile readout equal to `profile(core.base)`.  Hence
any S2456 paper family whose hull is below that value is impossible: coverage
gives a member, and `upper` would force the constant profile value below the
hull.  This is a formal obstruction, independent of q. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual
open LeanFormal.IUT.XiFPaper.S2456PaperFamilyActual
open LeanFormal.IUT.XiFPaper.S2510PaperFamilyCandidateActual

namespace LeanFormal.IUT.XiFPaper.S2511PaperFamilyObstruction

universe u v ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice] [Fintype Label]
variable {X : Type ux} {P : PaperSignedHull X Label}
variable {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}

theorem S2511_no_family_of_hull_lt
    (h : P.signedHullLogVolume <
      R.input.profile.logVolume R.input.core.base) :
    ¬ Nonempty (S2456ActualPaperFamilyRequired P R) := by
  rintro ⟨F⟩
  obtain ⟨D, hD⟩ := F.P_C_nonempty
  have hread := F.readout_eq D hD
  have hupper := F.upper D hD
  rw [hread, S2510_profile_const D] at hupper
  linarith

#check S2511_no_family_of_hull_lt

end LeanFormal.IUT.XiFPaper.S2511PaperFamilyObstruction
end
