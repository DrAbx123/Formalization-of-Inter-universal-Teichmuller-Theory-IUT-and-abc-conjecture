import tmp.sheaf.xif.paper.S2096StackMorphismActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2151: S2096 vertex-square two-pullback: exact missing from full properties

S2096UnpastingStatement asks for a weak `TwoPullbackWitness` of the vertex
square from two weak base-change presentations.  The tree has the full
2-universal property only as an extra strong structure
(`S1852ConeEssSurj` / `S1827EssSurjOf`); it does not produce the weak witness
without the reverse-pasting/right-cancellation step.

This file records the exact missing implication as Type-valued data.  No
inhabitant is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2151UnpastingActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

universe u

/-- Exact missing implication: full cone essential-surjectivity of the two
presentations gives the weak two-pullback witness of the vertex square. -/
def S2151UnpastingOfFull : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Py : EtaleStackBaseChangePresentation y T
      (Pseudofunctor.StrongTrans.vcomp ptY y))
    (Px : EtaleStackBaseChangePresentation (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y)),
    S1827EssSurjOf (S1852WeakSquare Py) Py.isPullback →
    S1827EssSurjOf (S1852WeakSquare Px) Px.isPullback →
    (S2096VertexSquare (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
      (Px := Px)).TwoPullbackWitness

#check S2151UnpastingOfFull

end LeanFormal.IUT.XiFPaper.S2151UnpastingActual

end
