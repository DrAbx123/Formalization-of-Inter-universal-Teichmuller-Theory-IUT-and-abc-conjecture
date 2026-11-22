import tmp.sheaf.xif.paper.S2519InvFunctorActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2539FaithfulActual

theorem S2539Faithful {C D : FiniteEtaleCover S2482AffineScheme} :
    Function.Injective (fun f : C ⟶ D => S2519InvFunctor.map f) := by
  intro f g h
  have hrel : S1728CoverMapRel (S2518InvCoverMap f) (S2518InvCoverMap g) := by
    have aux : ∀ a b : Iut.OrbicurveFiniteEtaleCoverMap
        (S2517InvObj C) (S2517InvObj D),
        Relation.EqvGen (fun f g => S1728CoverMapRel f g) a b →
        S1728CoverMapRel a b := by
      intro a b h
      induction h with
      | rel x y hr => exact hr
      | refl => exact S1728CoverMapRel_refl _
      | symm x y h ih => exact S1728CoverMapRel_symm ih
      | trans x y z h1 h2 ih1 ih2 => exact S1728CoverMapRel_trans ih1 ih2
    exact aux _ _ (Quot.eqvGen_exact h)
  rcases hrel with ⟨e⟩
  have hhom := S1742HomOfStrongTrans_congr e
  have hOver : S2518InvSchemeMap f = S2518InvSchemeMap g := by
    simpa only [S2518InvCoverMap, S1742HomOfStrongTrans_strongTransOfHom] using hhom
  have hleft : f.hom.left = g.hom.left := by
    change (S2518InvSchemeMap f).left = (S2518InvSchemeMap g).left
    exact congrArg CategoryTheory.Over.Hom.left hOver
  have hhom' : f.hom = g.hom := CategoryTheory.Over.OverMorphism.ext hleft
  exact InducedCategory.hom_ext hhom'

#check S2539Faithful
#print axioms S2539Faithful
end LeanFormal.IUT.XiFPaper.S2539FaithfulActual
end