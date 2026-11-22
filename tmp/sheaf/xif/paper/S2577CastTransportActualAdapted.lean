import tmp.sheaf.xif.paper.S2575CoverIsoActual
import tmp.sheaf.xif.paper.S2630CastHelpersActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2577CastTransportActualAdapted

variable {F : Type} [Field F]
variable {P Q R S : Iut.EtaleStackPseudofunctor F}

noncomputable def castStrongTrans2 (h : P = Q) (k : R = S)
    (L : Pseudofunctor.StrongTrans P R) :
    Pseudofunctor.StrongTrans Q S := by
  cases h
  cases k
  exact L

theorem castStrongTrans2_id (h : P = Q) :
    castStrongTrans2 h h (Pseudofunctor.StrongTrans.id P) =
      Pseudofunctor.StrongTrans.id Q := by
  cases h
  rfl

theorem castStrongTrans2_symm_cast (h : P = Q)
    (L : Pseudofunctor.StrongTrans P P) :
    castStrongTrans2 h.symm h.symm (castStrongTrans2 h h L) = L := by
  cases h
  rfl

theorem S2577X_eq_X0 {S : Iut.SchemeOverField S2480QiActual.F}
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (hS : X.source = S2517TStack S) :
    X = X0 S (hS.symm ▸ X.map) (hS.symm ▸ X.finiteEtale) := by
  cases X with
  | mk source map finiteEtale =>
    cases hS
    rfl

#print axioms castStrongTrans2
#print axioms S2577X_eq_X0

end LeanFormal.IUT.XiFPaper.S2577CastTransportActualAdapted
end
