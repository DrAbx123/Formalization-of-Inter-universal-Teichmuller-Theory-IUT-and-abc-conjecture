import tmp.sheaf.xif.paper.S2445SignProjectionActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2445SignProjectionActual
open LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2446SignProjectionGeneralActualAdapted

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

theorem S2446_signProjection : S2427SignProjection S M N := by
  intro T₁ T₂ p x
  apply Subtype.ext
  simp [S2427Comp, S2332Psub, S2152Q, S2152PFunctor, Pseudofunctor.presheafHom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom, S1971PrecompFunctor_map_val]

#print axioms S2446_signProjection

end LeanFormal.IUT.XiFPaper.S2446SignProjectionGeneralActualAdapted

end
