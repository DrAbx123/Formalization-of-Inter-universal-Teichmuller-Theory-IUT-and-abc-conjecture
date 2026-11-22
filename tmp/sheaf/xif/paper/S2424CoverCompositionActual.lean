import tmp.sheaf.xif.paper.S2403RepresentableExamplesActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual
namespace LeanFormal.IUT.XiFPaper.S2424CoverCompositionActual

structure S2424ComposableRepresentable
    {A B C : S1728Cover} (g1 : S1728CoverMap A B) (g2 : S1728CoverMap B C) where
  R1 : S2403RepresentableCoverMap g1
  R2 : S2403RepresentableCoverMap g2
  middle_eq : R1.targetScheme = R2.sourceScheme

/-- Exact composite representability data.  The scheme-level composite map is
recorded explicitly to avoid a dependent cast in the field type. -/
structure S2424CompositeRepresentable
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) where
  sourceScheme : SchemeOverField S1726K
  targetScheme : SchemeOverField S1726K
  source_fiber_eq : A.source.fiber = S1742YS (F := S1726K) sourceScheme
  target_fiber_eq : C.source.fiber = S1742YS (F := S1726K) targetScheme
  g0 : sourceScheme ⟶ targetScheme
  map_iso : Nonempty (Iso
    (S2403CastHom source_fiber_eq target_fiber_eq (S1641CoverMapComp g1 g2).map)
    (S1742StrongTransOfHom (F := S1726K) g0))
  mono : Mono g0

def S2424CompositionRequired
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) : Prop :=
  Nonempty (S2424CompositeRepresentable H)

end LeanFormal.IUT.XiFPaper.S2424CoverCompositionActual
end