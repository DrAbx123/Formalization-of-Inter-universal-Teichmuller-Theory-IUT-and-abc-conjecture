import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual

namespace Probe

#check Pseudofunctor.StrongTrans.isoMk
#check CategoryTheory.Cat.Hom.isoMk
#check CategoryTheory.Cat.Hom.toNatIso
#check CategoryTheory.Cat.Hom₂.ext
#check CategoryTheory.Cat.ext
#check CategoryTheory.Pseudofunctor.StrongTrans.mkOfOplax
#check Pseudofunctor.StrongTrans.id
#check Pseudofunctor.StrongTrans.vcomp
#check Pseudofunctor.StrongTrans.naturality_comp_hom
#check Pseudofunctor.StrongTrans.naturality_id_hom

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

example (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (sitePseudofunctor f g).obj U = S1890IsoCommaObj f g U := rfl

example {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (sitePseudofunctor f g).map φ = S1890IsoCommaMap f g φ := rfl

-- try to construct toA
noncomputable def toA : Pseudofunctor.StrongTrans (sitePseudofunctor f g) A.source.fiber where
  app U := (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).toCatHom
  naturality {U V} φ := by
    -- goal Iso ((sitePseudofunctor f g).map φ ≫ app V) (app U ≫ A.source.fiber.map φ)
    -- in Cat, types are functors; show equality via Cat.ext
    apply eqToIso
    apply CategoryTheory.Cat.ext
    -- here should be functor equality
    sorry
  naturality_naturality := by
    intro a b f g_1 eta
    sorry
  naturality_id := by
    intro a
    sorry
  naturality_comp := by
    intro a b c f g_1
    sorry

end Probe
