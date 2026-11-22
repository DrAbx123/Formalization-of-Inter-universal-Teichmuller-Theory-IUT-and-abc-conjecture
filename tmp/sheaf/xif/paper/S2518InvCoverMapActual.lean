import tmp.sheaf.xif.paper.S2517InvObjActual
import tmp.sheaf.xif.paper.S2517StackPresentationActual
import tmp.sheaf.xif.paper.S2517RepresentableFiniteEtaleActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2517StackPresentationActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual

noncomputable def S2518InvSchemeMap {C D : FiniteEtaleCover S2482AffineScheme}
    (f : C ⟶ D) : S2517CScheme C ⟶ S2517CScheme D :=
  Over.homMk f.hom.left (by
    change f.hom.left ≫ (D.obj.hom ≫ S2482AffineOver.hom) =
      C.obj.hom ≫ S2482AffineOver.hom
    rw [← Category.assoc, f.hom.w])

noncomputable def S2518InvCoverMap {C D : FiniteEtaleCover S2482AffineScheme}
    (f : C ⟶ D) :
    Iut.OrbicurveFiniteEtaleCoverMap (S2517InvObj C) (S2517InvObj D) where
  map := S1742StrongTransOfHom (S2518InvSchemeMap f)
  commutes := by
    let φ := S2518InvSchemeMap f
    let eta : Pseudofunctor.StrongTrans
        (Iut.schemeRepresentableEtalePseudofunctor F (S2517CScheme C))
        (Iut.schemeRepresentableEtalePseudofunctor F S2517S) :=
      Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom φ)
        (S1742StrongTransOfHom (S2517OverMap D))
    have hcomp :
        S1742HomOfStrongTrans eta = S2517OverMap C := by
      dsimp [eta]
      rw [S1742HomOfStrongTrans_vcomp, S1742HomOfStrongTrans_strongTransOfHom,
        S1742HomOfStrongTrans_strongTransOfHom]
      -- scheme morphism equality
      apply CategoryTheory.Over.OverMorphism.ext
      exact f.hom.w
    exact (S1742StrongTransIsoOfHom eta).symm.trans
      (eqToIso (congrArg S1742StrongTransOfHom hcomp))

#check S2518InvCoverMap
#print axioms S2518InvCoverMap
end LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
end