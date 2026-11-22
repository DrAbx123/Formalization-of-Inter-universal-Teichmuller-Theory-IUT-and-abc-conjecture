import tmp.sheaf.xif.paper.S2511PaperFamilyObstruction
import tmp.sheaf.xif.paper.S2512PaperFamilySignedActual

/-! # S2513: exact characterization of the paper family

The S2456 paper family exists if and only if the actual profile value at the
core base is bounded by the paper signed hull.  S2512 gives the construction,
S2511 gives the obstruction. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S2456PaperFamilyActual
open LeanFormal.IUT.XiFPaper.S2511PaperFamilyObstruction
open LeanFormal.IUT.XiFPaper.S2512PaperFamilySignedActual

namespace LeanFormal.IUT.XiFPaper.S2513PaperFamilyCharacterization

universe u v ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice] [Fintype Label]
variable {X : Type ux} {P : PaperSignedHull X Label}
variable {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}

theorem S2513_family_iff_hull :
    Nonempty (S2456ActualPaperFamilyRequired P R) ↔
      R.input.profile.logVolume R.input.core.base ≤
        P.signedHullLogVolume := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact S2511_no_family_of_hull_lt hlt h
  · intro hbound
    exact ⟨S2512PaperFamilySigned hbound⟩

#check S2513_family_iff_hull

end LeanFormal.IUT.XiFPaper.S2513PaperFamilyCharacterization
end
