import tmp.sheaf.xif.paper.S2242DiffProductActual

-- S2248: diff invariance surface.  The transported leftQuotientEquiv
-- identity is actual (S2242); the product reindexing is the exact
-- remaining missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2248DiffInvarianceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual

universe u

/-- Exact missing: diff/transfer product invariance on transported
transversals. -/
abbrev S2248DiffInvarianceRequired : Prop :=
  S2226DiffTransportRequired.{u}

#check S2248DiffInvarianceRequired

end LeanFormal.IUT.XiFPaper.S2248DiffInvarianceActual

end