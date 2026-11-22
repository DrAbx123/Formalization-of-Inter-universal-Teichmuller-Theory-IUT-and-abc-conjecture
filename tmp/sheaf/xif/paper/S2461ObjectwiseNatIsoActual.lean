import tmp.sheaf.xif.paper.S2312EqualizerIsoFinal2Actual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2461ObjectwiseNatIsoActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

noncomputable def S2461Iso :
    S2152Q.presheafHom M N ≅
      Limits.equalizer (S2285f S M) (S2285g S N) :=
  NatIso.ofComponents (fun T => S2312QHomEqualizerObjIso S M N T) (by
    intro T₁ T₂ p
    ext x
    rfl)

#print axioms S2461Iso

end LeanFormal.IUT.XiFPaper.S2461ObjectwiseNatIsoActual

end
