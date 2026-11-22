import tmp.sheaf.xif.paper.S2926CorrectedCompletionPackagingActual
import tmp.sheaf.xif.paper.S2905CoreWithHqW
import tmp.sheaf.xif.paper.S2908CorrectedSActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2905CoreWithHqW
open LeanFormal.IUT.XiFPaper.S2892CoreWithQActual
open LeanFormal.IUT.XiFPaper.S2908CorrectedSActual
open LeanFormal.IUT.XiFPaper.S2925SourceCompletionCorrectedActual
open LeanFormal.IUT.XiFPaper.S2926CorrectedCompletionPackagingActual
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
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

namespace LeanFormal.IUT.XiFPaper.S2927CorrectedCompletionDownstreamActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Corrected completion whose sign quotient is the S2908 corrected S built
from S2905Core. -/
noncomputable def S2927Completion
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
    (I2892 : S2892Inputs hQ
      (S2869SignAction D atBase generator_identification) W)
    (I : S2926Inputs
      (S2908CorrectedS hQ D atBase generator_identification W I2892)) :
    SourceCompletionCorrected :=
  S2926Completion
    (S2908CorrectedS hQ D atBase generator_identification W I2892) I

theorem S2927Completion_signQuotient
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
    (I2892 : S2892Inputs hQ
      (S2869SignAction D atBase generator_identification) W)
    (I : S2926Inputs
      (S2908CorrectedS hQ D atBase generator_identification W I2892)) :
    (S2927Completion hQ D atBase generator_identification W I2892 I).signQuotient =
      S2908CorrectedS hQ D atBase generator_identification W I2892 :=
  rfl

/-- Downstream consumers that must move to the corrected completion. -/
def S2927DownstreamConsumers : List String :=
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

#check S2927Completion
#check S2927Completion_signQuotient
#check S2927DownstreamConsumers
#print axioms S2927Completion
#print axioms S2927Completion_signQuotient

end LeanFormal.IUT.XiFPaper.S2927CorrectedCompletionDownstreamActual
end
