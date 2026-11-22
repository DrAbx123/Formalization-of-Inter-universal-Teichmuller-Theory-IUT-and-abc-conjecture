import tmp.sheaf.xif.paper.S2266DiffProductReindexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2279DiffExplicitBijActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2266DiffProductReindexActual

universe u

abbrev S2279DiffExplicitBijRequired : Prop :=
  S2226DiffTransportRequired.{u}

#check S2279DiffExplicitBijRequired

end LeanFormal.IUT.XiFPaper.S2279DiffExplicitBijActual

end