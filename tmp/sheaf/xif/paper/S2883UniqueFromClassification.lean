import tmp.sheaf.xif.paper.S2877UniqueReductionAudit
import tmp.sheaf.xif.paper.S2880CorrectedA6CoreNontrivialActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
open LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Inputs reducing S2880's unique-involution field: the exact classification
plus the statement that the underlying scheme map is nontrivial iff the stack
endomorphism is nontrivial. -/
structure S2883Inputs where
  classification : S2877OrderTwoAutClassification
  underlying_ne_id_iff :
    ∀ inv : S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
        S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      S2877Underlying inv ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X ↔
        inv ≠ Iut.HyperbolicOrbicurve.Hom.id
          S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve

theorem S2883_unique
    (I : S2883Inputs)
    (inv : S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (hsq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id
        S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve))
    (hnt : inv ≠ Iut.HyperbolicOrbicurve.Hom.id
      S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) :
    Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv (S2857StackAuto alphaOverS2844)) :=
  S2877_unique_of_classification I.classification inv hsq
    ((I.underlying_ne_id_iff inv).mpr hnt)

/-- Replace S2880's unique-involution input by the classification-derived one. -/
noncomputable def S2883_toS2880
    (I : S2883Inputs)
    (signAction : Iut.OrbicurveSignAction
      S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (J : S2880Inputs signAction) : S2880Inputs signAction :=
  { J with
    unique_elliptic_involution := by
      intro inv hsq hnt
      exact S2883_unique I inv hsq hnt }

#check S2883Inputs
#check S2883_unique
#check S2883_toS2880

end LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
end
