import tmp.sheaf.xif.paper.S2518InvCoverMapActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
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
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2519InvFunctorActual

noncomputable def S2519InvFunctor :
    FiniteEtaleCover S2482AffineScheme ⥤
      Iut.OrbicurveFiniteEtaleCover S2482Orbicurve where
  obj := S2517InvObj
  map f := Quot.mk _ (S2518InvCoverMap f)
  map_id := by
    intro C
    apply Quot.sound
    let first := S2518InvCoverMap (𝟙 C)
    have hfirst : S1742HomOfStrongTrans first.map = 𝟙 (S2517CScheme C) := by
      dsimp [first, S2518InvCoverMap, S2518InvSchemeMap]
      rw [S1742HomOfStrongTrans_strongTransOfHom]
      apply CategoryTheory.Over.OverMorphism.ext
      rfl
    exact ⟨(S1742StrongTransIsoOfHom first.map).symm.trans
      ((eqToIso (congrArg S1742StrongTransOfHom hfirst)).trans
        (S1742StrongTransIsoOfHom
          (Pseudofunctor.StrongTrans.id (S2517InvObj C).source.fiber)))⟩
  map_comp := by
    intro C D E f g
    apply Quot.sound
    let first := S2518InvCoverMap (f ≫ g)
    let second := S1641CoverMapComp
      (S2518InvCoverMap (C := C) (D := D) f)
      (S2518InvCoverMap (C := D) (D := E) g)
    have hhom : S1742HomOfStrongTrans first.map =
        S1742HomOfStrongTrans second.map := by
      dsimp [first, second, S2518InvCoverMap, S1641CoverMapComp]
      rw [S1742HomOfStrongTrans_strongTransOfHom]
      have hv := S1742HomOfStrongTrans_vcomp
        (S1742StrongTransOfHom (S2518InvSchemeMap f))
        (S1742StrongTransOfHom (S2518InvSchemeMap g))
      rw [hv]
      rw [S1742HomOfStrongTrans_strongTransOfHom,
        S1742HomOfStrongTrans_strongTransOfHom]
      apply CategoryTheory.Over.OverMorphism.ext
      rfl
    refine ⟨(S1742StrongTransIsoOfHom first.map).symm.trans
      ((eqToIso (congrArg S1742StrongTransOfHom hhom)).trans
        (S1742StrongTransIsoOfHom second.map))⟩

#check S2519InvFunctor
end LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
end