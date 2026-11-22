import tmp.sheaf.xif.paper.S2305SubgroupOfMapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2311OpenComapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2305SubgroupOfMapActual

universe u

theorem S2311_mem_comap_toSubgroup {G N : Type u} [Group G] [Group N]
    [TopologicalSpace G] [TopologicalSpace N]
    (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) (x : G) :
    x ∈ (H.comap f hf : Subgroup G) ↔ f x ∈ H :=
  OpenSubgroup.mem_comap

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev S2311SubgroupOfMapRequired : Prop :=
  S2300SubgroupOfMapRequired (p := p)

#check S2311_mem_comap_toSubgroup
#check S2311SubgroupOfMapRequired
#print axioms S2311_mem_comap_toSubgroup

end LeanFormal.IUT.XiFPaper.S2311OpenComapActual

end