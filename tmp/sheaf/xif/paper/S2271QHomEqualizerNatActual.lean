import tmp.sheaf.xif.paper.S2267QHomEqualizerMulActionActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual

variable (S : Iut.SchemeOverField S1726K)

/-- Pointwise subtype formula for the Q hom-presheaf, using the explicit
S2267 action and S1971PointwiseQuotient_hom. -/
theorem S2271QHomObj_eq_subtype
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    (S2152Q.presheafHom M N).obj T =
      {g : Iut.SignGroup // g • S2267PT S M T = S2267QT S N T} := by
  letI := S2267PointMulAction S T
  let a := (T.unop.hom.op).toLoc
  let P : S2152Q.obj (LocallyDiscrete.mk (Opposite.op T.unop.left)) :=
    (S2152Q.map a).toFunctor.obj M
  let Qv : S2152Q.obj (LocallyDiscrete.mk (Opposite.op T.unop.left)) :=
    (S2152Q.map a).toFunctor.obj N
  change (P ⟶ Qv) = {g : Iut.SignGroup // g • P.back = Qv.back}
  exact S1971PointwiseQuotient_hom (U := LocallyDiscrete.mk (Opposite.op T.unop.left)) P Qv

#print axioms S2271QHomObj_eq_subtype

end LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual

end
