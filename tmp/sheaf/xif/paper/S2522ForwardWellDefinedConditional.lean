import tmp.sheaf.xif.paper.S2519ForwardFunctorPartialActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivMapActual
open LeanFormal.IUT.XiFPaper.S2519ForwardFunctorPartialActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2522ForwardWellDefinedConditional

/-- The exact remaining map-level equality needed for quotient descent. -/
def S2522MissingMapHomEq : Prop :=
  ∀ {C D : S2519SourceCategory}
    {φ ψ : Iut.OrbicurveFiniteEtaleCoverMap C D},
    S1728CoverMapRel φ ψ →
      S2517MapHom φ = S2517MapHom ψ

theorem S2522WellDefined_of_mapHomEq
    (h : S2522MissingMapHomEq) :
    S2519ForwardMapWellDefined := by
  intro C D φ ψ hrel
  apply ObjectProperty.hom_ext
  apply CategoryTheory.Over.OverMorphism.ext
  exact congrArg (fun e => e.left) (h hrel)

#check S2522WellDefined_of_mapHomEq
#print axioms S2522WellDefined_of_mapHomEq
end LeanFormal.IUT.XiFPaper.S2522ForwardWellDefinedConditional
end