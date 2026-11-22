import tmp.sheaf.xif.paper.S2905CoreWithHqW
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2905CoreWithHqW
open LeanFormal.IUT.XiFPaper.S2892CoreWithQActual
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2908CorrectedSActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- The corrected S-layer interface: exactly the corrected sign-quotient record. -/
abbrev CorrectedS := SourceSignQuotientDataCorrected S2847A6

/-- Build the corrected S layer from S2905Core's corrected data. -/
noncomputable def S2908CorrectedS
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K))
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2870QuotientWitnessData S2882A6Q hQ
      (S2869SignAction D atBase generator_identification))
    (I : S2892Inputs hQ
      (S2869SignAction D atBase generator_identification) W) :
    CorrectedS :=
  S2905Core hQ D atBase generator_identification W I

/-- Corrected S layer has the weakened uniqueness and explicit nontriviality. -/
theorem S2908_corrected_unique
    (D : CorrectedS) :
    D.ellipticInvolution ≠
        Iut.HyperbolicOrbicurve.Hom.id D.xF ∧
      ∀ inv : D.xF.Hom D.xF,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id D.xF) →
        inv ≠ Iut.HyperbolicOrbicurve.Hom.id D.xF →
        Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv D.ellipticInvolution) :=
  ⟨D.ellipticInvolution_nontrivial, D.unique_elliptic_involution⟩

/-- Downstream consumers that must be replayed against the corrected S layer. -/
def S2908DownstreamConsumers : List String :=
  [ "S2848A6CompletionConditionalActual"
  , "S2858A6SFromCore"
  , "S2859A6CoreActualInvolution"
  , "S2860A6CoreWithSignActionConditional"
  , "S2867A6CoreActualInvolutionSignAction"
  , "S2869A6CoreWithGenericQuotient"
  , "S2880CorrectedA6CoreNontrivialActual"
  , "S2887CorrectedCoreMinimalActual"
  , "S2892CoreWithQActual"
  , "S2902CoreWithQMinimalActual"
  , "S2905CoreWithHqW" ]

#check CorrectedS
#check S2908CorrectedS
#check S2908_corrected_unique
#check S2908DownstreamConsumers
#print axioms S2908CorrectedS
#print axioms S2908_corrected_unique

end LeanFormal.IUT.XiFPaper.S2908CorrectedSActual
end
