import tmp.sheaf.xif.paper.S2876NontrivialAlphaActual
import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2855A6CoreFromD6ConditionalActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2876NontrivialAlphaActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2879NontrivialStackAutoActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF

theorem S2879_homOfStrongTrans_id :
    S1742HomOfStrongTrans (F := S2847A6.F)
      (Iut.HyperbolicOrbicurve.Hom.id S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) =
      𝟙 S2844D6F6BaseChangeActual.S2844X := by
  change (((Iut.HyperbolicOrbicurve.Hom.id S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve).app
      (LocallyDiscrete.mk (Opposite.op S2844D6F6BaseChangeActual.S2844X))).toFunctor.obj
      (Discrete.mk (𝟙 S2844D6F6BaseChangeActual.S2844X))).as =
    𝟙 S2844D6F6BaseChangeActual.S2844X
  rfl

theorem S2879_nontrivial :
    S2857StackAuto alphaOverS2844 ≠
      Iut.HyperbolicOrbicurve.Hom.id S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve := by
  intro h
  have hα : alphaOverS2844 = 𝟙 S2844D6F6BaseChangeActual.S2844X := by
    have h' := congrArg
      (S1742HomOfStrongTrans (F := S2847A6.F)) h
    rwa [S2857StackAuto, S1742HomOfStrongTrans_strongTransOfHom,
      S2879_homOfStrongTrans_id] at h'
  exact S2876_alphaOverS2844_ne_id hα

#check S2879_nontrivial
#print axioms S2879_nontrivial

end LeanFormal.IUT.XiFPaper.S2879NontrivialStackAutoActual
end
