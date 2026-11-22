import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2516StackOpenImmersionActual

/-- Final representable open-immersion statement for the UB affine chart. -/
noncomputable def S2516OpenImmersion :
    Iut.EtaleStackOpenImmersion S2508StackOpenMap :=
  S2512StackOpenImmersion

#print axioms S2516OpenImmersion

end LeanFormal.IUT.XiFPaper.S2516StackOpenImmersionActual
end
