import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S2403RepresentableExamplesActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S2409StrongCoverRepresentableActual

theorem S2409TerminalStrong_source_fiber :
    (StrongCover.cover S1852TerminalStrong).source.fiber =
      S1742YS (F := S1726K) S1726AffineOver := rfl

theorem S2409TerminalStrong_map :
    (S1641CoverMapId (StrongCover.cover S1852TerminalStrong)).map =
      Pseudofunctor.StrongTrans.id
        (StrongCover.cover S1852TerminalStrong).source.fiber :=
  S1641CoverMapId_map (StrongCover.cover S1852TerminalStrong)

noncomputable def S2409TerminalStrongRepresentable :
    S2403RepresentableCoverMap
      (S1641CoverMapId (StrongCover.cover S1852TerminalStrong)) where
  sourceScheme := S1726AffineOver
  targetScheme := S1726AffineOver
  source_fiber_eq := rfl
  target_fiber_eq := rfl
  g0 := 𝟙 S1726AffineOver
  map_iso := by
    refine ⟨?_⟩
    change Iso ((S1641CoverMapId (StrongCover.cover S1852TerminalStrong)).map)
      (S1742StrongTransOfHom (F := S1726K) (𝟙 S1726AffineOver))
    rw [S2409TerminalStrong_map]
    have hhom : S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S1726AffineOver)) =
        𝟙 S1726AffineOver := by
      unfold S1742HomOfStrongTrans
      rfl
    have e := S1742StrongTransIsoOfHom
      (eta := Pseudofunctor.StrongTrans.id (S1742YS (F := S1726K) S1726AffineOver))
    rw [hhom] at e
    exact e.symm
  mono := inferInstance

end LeanFormal.IUT.XiFPaper.S2409StrongCoverRepresentableActual
end