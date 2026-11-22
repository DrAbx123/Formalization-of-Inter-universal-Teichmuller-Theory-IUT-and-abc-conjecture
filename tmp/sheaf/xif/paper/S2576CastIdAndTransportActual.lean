import tmp.sheaf.xif.paper.S2575CoverIsoActual
import tmp.sheaf.xif.paper.S2630CastHelpersActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2576CastIdAndTransportActual

variable {F : Type} [Field F]
variable {P Q R : Iut.EtaleStackPseudofunctor F}

theorem castStrongTrans_id (h : P = Q) :
    castStrongTrans h (Pseudofunctor.StrongTrans.id P) =
      Pseudofunctor.StrongTrans.id Q := by
  cases h
  rfl

theorem castStrongTrans_symm_cast (h : P = Q)
    (L : Pseudofunctor.StrongTrans P R) :
    castStrongTrans h.symm (castStrongTrans h L) = L := by
  cases h
  rfl

theorem S2576X_eq_X0 {S : Iut.SchemeOverField S2480QiActual.F}
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (hS : X.source = S2517TStack S) :
    X = X0 S X.map X.finiteEtale := by
  cases X with
  | mk source map finiteEtale =>
    cases hS
    rfl

#print axioms castStrongTrans_id
#print axioms castStrongTrans_symm_cast
#print axioms S2576X_eq_X0

end LeanFormal.IUT.XiFPaper.S2576CastIdAndTransportActual
end
