import tmp.sheaf.xif.paper.S2400CoverRepresentableActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S2291UniformGraphCompatActual
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
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual

/-- Transport a stack hom to the representable model along fiber equalities. -/
def S2403CastHom {A B : EtaleStackOverField S1726K}
    {S T : SchemeOverField S1726K}
    (hA : A.fiber = S1742YS (F := S1726K) S)
    (hB : B.fiber = S1742YS (F := S1726K) T)
    (g : A.Hom B) :
    Pseudofunctor.StrongTrans (S1742YS (F := S1726K) S)
      (S1742YS (F := S1726K) T) :=
  hA.symm ▸ hB.symm ▸ g

/-- Representable cover map with an explicit iso to the S1742 representable
strong transformation. -/
structure S2403RepresentableCoverMap
    {A B : S1728Cover} (g : S1728CoverMap A B) where
  sourceScheme : SchemeOverField S1726K
  targetScheme : SchemeOverField S1726K
  source_fiber_eq : A.source.fiber = S1742YS (F := S1726K) sourceScheme
  target_fiber_eq : B.source.fiber = S1742YS (F := S1726K) targetScheme
  g0 : sourceScheme ⟶ targetScheme
  map_iso : Nonempty (Iso
    (S2403CastHom source_fiber_eq target_fiber_eq g.map)
    (S1742StrongTransOfHom (F := S1726K) g0))
  mono : Mono g0

theorem S2403PathCover_source_fiber :
    S2291PathCover.source.fiber = S1742YS (F := S1726K) S1726AffineOver := rfl

theorem S2403PathCoverId_map :
    (S1641CoverMapId S2291PathCover).map =
      Pseudofunctor.StrongTrans.id S2291PathCover.source.fiber :=
  S1641CoverMapId_map S2291PathCover

/-- The identity cover map of the S2291 path cover is represented by the
identity scheme map of S1726AffineOver, up to the S1742 round-trip iso, and is
monic. -/
noncomputable def S2403PathCoverIdRepresentable :
    S2403RepresentableCoverMap (S1641CoverMapId S2291PathCover) where
  sourceScheme := S1726AffineOver
  targetScheme := S1726AffineOver
  source_fiber_eq := rfl
  target_fiber_eq := rfl
  g0 := 𝟙 S1726AffineOver
  map_iso := by
    refine ⟨?_⟩
    change Iso ((S1641CoverMapId S2291PathCover).map)
      (S1742StrongTransOfHom (F := S1726K) (𝟙 S1726AffineOver))
    rw [S2403PathCoverId_map]
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

end LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual
end
