import tmp.sheaf.xif.paper.S2876CorrectedA6CoreActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- The underlying scheme endomorphism of a stack endomorphism of the A6
orbicurve, via the S1742 2-Yoneda comparison. -/
noncomputable def S2877Underlying
    (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) :
    S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X :=
  S1742HomOfStrongTrans (F := S2847A6.F) inv

/-- The exact missing classification: every order-two scheme automorphism of
S2844X is the identity or the actual chart alpha automorphism. -/
def S2877OrderTwoAutClassification : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
      β = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨ β = alphaOverS2844

/-- Conditional actual reduction: the classified order-two scheme automorphism
yields the weakened corrected uniqueness for stack involutions. -/
theorem S2877_unique_of_classification
    (hclass : S2877OrderTwoAutClassification)
    (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (hsq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve))
    (hnt : S2877Underlying inv ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X) :
    Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv (S2857StackAuto alphaOverS2844)) := by
  let β := S2877Underlying inv
  have hβ2 : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X := by
    have h1 : S1742HomOfStrongTrans (F := S2847A6.F)
        (Pseudofunctor.StrongTrans.vcomp inv inv) =
        S1742HomOfStrongTrans (F := S2847A6.F) inv ≫
          S1742HomOfStrongTrans (F := S2847A6.F) inv :=
      S1742HomOfStrongTrans_vcomp (F := S2847A6.F) inv inv
    have h2 : S1742HomOfStrongTrans (F := S2847A6.F)
        (Pseudofunctor.StrongTrans.vcomp inv inv) =
        S1742HomOfStrongTrans (F := S2847A6.F)
          (Iut.HyperbolicOrbicurve.Hom.id
            LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) := by
      exact S1742HomOfStrongTrans_congr (F := S2847A6.F)
        (S := S2844D6F6BaseChangeActual.S2844X)
        (T := S2844D6F6BaseChangeActual.S2844X) hsq
    have hid : S1742HomOfStrongTrans (F := S2847A6.F)
        (Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) =
        𝟙 S2844D6F6BaseChangeActual.S2844X := rfl
    exact h1.symm.trans (h2.trans hid)
  rcases hclass β hβ2 with hid | halpha
  · exact absurd hid hnt
  · have hiso := S1742StrongTransIsoOfHom (F := S2847A6.F) inv
    rw [show S1742HomOfStrongTrans (F := S2847A6.F) inv =
        alphaOverS2844 from halpha] at hiso
    exact ⟨hiso.symm⟩

#check S2877Underlying
#check S2877OrderTwoAutClassification
#check S2877_unique_of_classification
#print axioms S2877_unique_of_classification

end LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
end
