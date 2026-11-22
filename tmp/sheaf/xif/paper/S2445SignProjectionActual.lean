import tmp.sheaf.xif.paper.S2427PsubNatIsoConditionalActual
import tmp.sheaf.xif.paper.S2425NatIsoCastHelpersActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2445SignProjectionActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

/-- Special case p = 1: the S2271 cast component commutes with the identity
restriction. -/
theorem S2445_signProjection_id
    (x : (S2152Q.presheafHom M N).obj T) :
    (S2427Comp S M N T).hom ((S2152Q.presheafHom M N).map (𝟙 T) x) =
      (S2332Psub S M N).map (𝟙 T) ((S2427Comp S M N T).hom x) := by
  simp [S2427Comp, S2332Psub, S2152Q, S2152PFunctor, Pseudofunctor.presheafHom]

#print axioms S2445_signProjection_id

end LeanFormal.IUT.XiFPaper.S2445SignProjectionActual

end
