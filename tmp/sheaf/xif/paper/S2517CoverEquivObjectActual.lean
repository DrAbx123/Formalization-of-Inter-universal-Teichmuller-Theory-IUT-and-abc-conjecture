import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open Iut
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual

abbrev S2517Cover : Type 1 := OrbicurveFiniteEtaleCover S2482Orbicurve

/-- The identity scheme-valued point of the representable stack of S2482AffineOver. -/
noncomputable def S2517Point :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver)
      S2482Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- Object map: base change a finite etale cover of the S2482 orbicurve along the
identity point; its pullback scheme is a finite etale cover of the affine scheme. -/
noncomputable def S2517Obj (C : S2517Cover) : FiniteEtaleCover S2482AffineScheme :=
  let bc := C.finiteEtale.baseChange S2482AffineOver S2517Point
  ⟨Over.mk bc.projection.left,
    (C.finiteEtale.hasProperty S2482AffineOver S2517Point).2,
    (C.finiteEtale.hasProperty S2482AffineOver S2517Point).1⟩

#check S2517Obj
#print axioms S2517Obj

end LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
end
