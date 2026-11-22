import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual
set_option backward.isDefEq.respectTransparency false
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
variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
example (a : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1836IsoCommaFst (f.map.app a).toFunctor (g.map.app a).toFunctor).toCatHom.toFunctor
      = S1836IsoCommaFst (f.map.app a).toFunctor (g.map.app a).toFunctor := rfl
example (a : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1836IsoCommaFst (f.map.app a).toFunctor (g.map.app a).toFunctor).toCatHom.toFunctor
      = S1836IsoCommaFst (f.map.app a).toFunctor (g.map.app a).toFunctor := by
  rw [CategoryTheory.Functor.toCatHom_toFunctor]
end Probe
