import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual

noncomputable section
open LeanFormal.IUT CategoryTheory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2858CoherentDiagramPartialActual

open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF

abbrev S2858Fib := S2855HyperbolicOrbicurve.stack.fiber

/-- The object-level map of the candidate C2 action: identity on 1, the D6
stack automorphism on the nontrivial sign element. -/
noncomputable def S2858DMap
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    {b b' : Iut.SignActionIndex} (f : b ⟶ b') :
    Pseudofunctor.StrongTrans S2858Fib S2858Fib := by
  cases b; cases b'
  classical
  exact if h : f = 𝟙 _ then Pseudofunctor.StrongTrans.id S2858Fib
    else S2857StackAuto α

/-- The identity coherences of the candidate action. -/
noncomputable def S2858DMapId
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (b : Iut.SignActionIndex) :
    S2858DMap α (𝟙 b) ≅ Pseudofunctor.StrongTrans.id S2858Fib := by
  cases b
  classical
  simp only [S2858DMap]
  exact Iso.refl _

#check S2858DMap
#check S2858DMapId
#print axioms S2858DMap
#print axioms S2858DMapId


theorem S2858_signGroup_cases (g : Iut.SignGroup) :
    g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, g = Multiplicative.ofAdd a :=
    ⟨g.toAdd, (ofAdd_toAdd g).symm⟩
  rw [ha]
  fin_cases a
  · left; rfl
  · right; rfl

#check S2858_signGroup_cases
#print axioms S2858_signGroup_cases

end LeanFormal.IUT.XiFPaper.S2858CoherentDiagramPartialActual
end
