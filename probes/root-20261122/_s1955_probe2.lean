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
variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
noncomputable def toA : Pseudofunctor.StrongTrans (sitePseudofunctor f g) A.source.fiber where
  app U := (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).toCatHom
  naturality {U V} φ := by
    trace_state
    apply eqToIso
    apply CategoryTheory.Cat.ext
    trace_state
    sorry
  naturality_naturality := by
    intro a b f g_1 eta
    trace_state
    sorry
  naturality_id := by
    intro a
    trace_state
    sorry
  naturality_comp := by
    intro a b c f g_1
    trace_state
    sorry
end Probe
