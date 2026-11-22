import tmp.sheaf.xif.paper.S2518InvCoverMapActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
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

namespace LeanFormal.IUT.XiFPaper.S2519InvFunctorActual

/-- Partial inverse functor data: object and hom maps with identity compatibility. -/
structure S2520InvFunctorData where
  obj : FiniteEtaleCover S2482AffineScheme → Iut.OrbicurveFiniteEtaleCover S2482Orbicurve
  map : ∀ {C D : FiniteEtaleCover S2482AffineScheme}, (C ⟶ D) → (obj C ⟶ obj D)
  map_id : ∀ (C : FiniteEtaleCover S2482AffineScheme), map (𝟙 C) = 𝟙 (obj C)

noncomputable def S2520InvFunctorDataActual : S2520InvFunctorData where
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

end LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
end