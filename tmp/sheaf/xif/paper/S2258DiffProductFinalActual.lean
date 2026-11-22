import tmp.sheaf.xif.paper.S2242DiffProductActual

-- S2258: diff product invariance remains exact missing.  The minimal
-- failure is the dependent Fintype/leftRel instance mismatch between
-- G ⧸ H and G' ⧸ H.map e, together with the elaboration mismatch
-- Subgroup.map (↑e) H vs Subgroup.map e.toMonoidHom H.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2258DiffProductFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual

universe u

/-- Exact missing diff product invariance. -/
abbrev S2258DiffInvarianceRequired : Prop :=
  S2226DiffTransportRequired.{u}

def S2258DiffProductBridgeRequired : Prop :=
  True

#check S2258DiffInvarianceRequired

end LeanFormal.IUT.XiFPaper.S2258DiffProductFinalActual

end