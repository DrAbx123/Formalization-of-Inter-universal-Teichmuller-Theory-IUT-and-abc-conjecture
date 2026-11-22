import tmp.sheaf.xif.paper.S2096StackMorphismActual
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2156: S2096BaseChangeStatement and its exact missing APIs

S2096BaseChangeStatement asks: from a presentation `Q` of `m` at a point
`vy` over `A`, and a finite-etale morphism of test schemes `s : T -> A`,
construct a presentation of `m` at the base-changed point over `T`, with
finite-etale projection.

The tree has no API for:
1. base change of a `SchemeRepresentableMap` along an arbitrary scheme map;
2. base change of the weak `TwoPullbackWitness` of the presentation square.

Both are recorded below as exact Type-valued missing inputs.  No presentation
or witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2156S2096BaseChangeActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

universe u

/-- Exact missing API 1: a scheme-representable map base-changes along a
scheme square with given pullback projections. -/
def S2156SchemeRepresentableMapBaseChange : Type 1 :=
  ∀ {S A T : SchemeOverField S1726K} (g : S ⟶ A) (s : T ⟶ A)
    (R : SchemeOverField S1726K) (q : R ⟶ T) (r : R ⟶ S)
    (_hsq : r ≫ g = q ≫ s),
    SchemeRepresentableMap g →
    AlgebraicGeometry.IsFinite s.left →
    AlgebraicGeometry.Etale s.left →
    AlgebraicGeometry.IsFinite q.left →
    AlgebraicGeometry.Etale q.left →
    SchemeRepresentableMap q

#check S2156SchemeRepresentableMapBaseChange
#check S2096BaseChangeStatement

end LeanFormal.IUT.XiFPaper.S2156S2096BaseChangeActual

end
