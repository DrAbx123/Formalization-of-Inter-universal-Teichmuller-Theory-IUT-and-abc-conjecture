import tmp.sheaf.xif.paper.S2091SchemeDirectActual

/-! # S2092: morphisms of finite-etale stacks are representably finite etale

The exact remaining API for `g.map`: a morphism `m : X -> Y` over a base `Z`,
where both `X -> Z` and `Y -> Z` are representably finite etale, is itself
representably finite etale.  This is the stack-level analogue of
`S2091_scheme_finiteEtale_cancel_special`.  It cannot be obtained pointwise
from scheme cancellation without this representability statement.

No inhabitant is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2092FiniteEtaleStackMorphismActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual
open LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual
open LeanFormal.IUT.XiFPaper.S2091SchemeDirectActual

universe u

/-- Exact missing stack-level API. -/
def S2092MorphismOfFiniteEtaleStacks : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K}
    (m : X.Hom Y) (y : Y.Hom Z) (x : X.Hom Z),
    Iso (Pseudofunctor.StrongTrans.vcomp m y) x →
    EtaleStackFiniteEtaleMorphism x →
    EtaleStackFiniteEtaleMorphism y →
    EtaleStackFiniteEtaleMorphism m

/-- The stack-level API gives `S2087GMapFiniteEtaleField` for `g.map`. -/
noncomputable def S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks
    (h : S2092MorphismOfFiniteEtaleStacks) : S2087GMapFiniteEtaleField := by
  dsimp only [S2087GMapFiniteEtaleField]
  intro A B C g
  exact h g.map C.map B.map g.commutes B.finiteEtale C.finiteEtale

#print axioms S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks

end LeanFormal.IUT.XiFPaper.S2092FiniteEtaleStackMorphismActual

end
