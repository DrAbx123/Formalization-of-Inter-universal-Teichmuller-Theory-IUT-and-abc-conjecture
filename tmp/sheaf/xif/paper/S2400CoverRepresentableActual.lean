import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S2400CoverRepresentableActual

/-- Exact representability data for a cover map: both source and target stack
fibers are representable, the map is induced by an actual scheme morphism, and
that scheme morphism is monic. -/
structure S2400RepresentableCoverMap
    {A B : S1728Cover} (g : S1728CoverMap A B) where
  sourceScheme : SchemeOverField S1726K
  targetScheme : SchemeOverField S1726K
  source_fiber_eq : A.source.fiber = S1742YS (F := S1726K) sourceScheme
  target_fiber_eq : B.source.fiber = S1742YS (F := S1726K) targetScheme
  g0 : sourceScheme ⟶ targetScheme
  map_heq : HEq g.map (S1742StrongTransOfHom (F := S1726K) g0)
  mono : Mono g0

/-- Exact first-missing proposition for a cover map. -/
def S2400RepresentableCoverMapRequired
    {A B : S1728Cover} (g : S1728CoverMap A B) : Prop :=
  Nonempty (S2400RepresentableCoverMap g)

end LeanFormal.IUT.XiFPaper.S2400CoverRepresentableActual
end