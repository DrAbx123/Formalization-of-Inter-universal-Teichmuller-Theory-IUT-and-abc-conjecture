import tmp.sheaf.xif.paper.S2266DiffProductReindexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2273DiffReindexFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2266DiffProductReindexActual

universe u

theorem S2273_map_bridge {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) : H.map (e : G →* G') = H.map e.toMonoidHom := rfl

abbrev S2273DiffInvarianceRequired : Prop :=
  S2226DiffTransportRequired.{u}

#check S2273_map_bridge
#check S2273DiffInvarianceRequired

end LeanFormal.IUT.XiFPaper.S2273DiffReindexFinalActual

end