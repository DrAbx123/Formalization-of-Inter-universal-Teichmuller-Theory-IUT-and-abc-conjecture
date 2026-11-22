import tmp.sheaf.xif.paper.S2332PsubCorrectActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

/-- Objectwise component Q hom → Psub, using S2271. -/
noncomputable def S2427Comp (T : (Over S)ᵒᵖ) :
    (S2152Q.presheafHom M N).obj T ≅ S2332Obj S M N T :=
  eqToIso (S2271QHomObj_eq_subtype S M N T)

/-- The exact naturality input for the Psub NatIso: the S2271 cast component is
natural with respect to Q hom restriction and Psub restriction. -/
def S2427SignProjection : Prop :=
  forall {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂)
    (x : (S2152Q.presheafHom M N).obj T₁),
    (S2427Comp S M N T₂).hom ((S2152Q.presheafHom M N).map p x) =
      (S2332Psub S M N).map p ((S2427Comp S M N T₁).hom x)

/-- Conditional construction of the Psub NatIso from the exact naturality
input. -/
noncomputable def S2427NatIso_of_signProjection
    (h : S2427SignProjection S M N) :
    S2152Q.presheafHom M N ≅ S2332Psub S M N :=
  NatIso.ofComponents (fun T => S2427Comp S M N T) (by
    intro T₁ T₂ p
    ext x
    exact h p x)

#print axioms S2427NatIso_of_signProjection

end LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual

end
