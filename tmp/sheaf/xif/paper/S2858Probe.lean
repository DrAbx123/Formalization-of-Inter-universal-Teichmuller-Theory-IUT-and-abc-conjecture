import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
noncomputable section
open LeanFormal.IUT CategoryTheory
namespace LeanFormal.IUT.XiFPaper.S2858Probe
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
abbrev Fib := S2855HyperbolicOrbicurve.stack.fiber
noncomputable def DMap (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    {b b' : CategoryTheory.SingleObj Iut.SignGroup} (f : b ⟶ b') : Fib ⟶ Fib := by
  cases b; cases b'
  exact if h : f = 1 then Pseudofunctor.StrongTrans.id Fib else S2857StackAuto α

noncomputable def DMapId (α) (b : CategoryTheory.SingleObj Iut.SignGroup) :
    DMap α (𝟙 b) ≅ 𝟙 Fib := by
  cases b
  simp [DMap]

#check DMap
#check DMapId
#print axioms DMapId
end LeanFormal.IUT.XiFPaper.S2858Probe