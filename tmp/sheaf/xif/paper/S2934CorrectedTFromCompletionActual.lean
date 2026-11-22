import tmp.sheaf.xif.paper.S2927CorrectedCompletionDownstreamActual
import tmp.sheaf.xif.paper.S2928CorrectedTConstructionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2905CoreWithHqW
open LeanFormal.IUT.XiFPaper.S2892CoreWithQActual
open LeanFormal.IUT.XiFPaper.S2908CorrectedSActual
open LeanFormal.IUT.XiFPaper.S2925SourceCompletionCorrectedActual
open LeanFormal.IUT.XiFPaper.S2926CorrectedCompletionPackagingActual
open LeanFormal.IUT.XiFPaper.S2927CorrectedCompletionDownstreamActual
open LeanFormal.IUT.XiFPaper.S2928CorrectedTConstructionActual
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

namespace LeanFormal.IUT.XiFPaper.S2934CorrectedTFromCompletionActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Corrected T constructed directly from S2927Completion. -/
noncomputable def S2934CorrectedT
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
    SourceNativeInitialThetaDataCorrected :=
  S2928CorrectedT_ofCompletion
    (S2927Completion hQ D atBase generator_identification W I2892 I)

theorem S2934CorrectedT_source
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
    (S2934CorrectedT hQ D atBase generator_identification W I2892 I).source =
      S2908CorrectedS hQ D atBase generator_identification W I2892 :=
  rfl

theorem S2934CorrectedT_arithmetic
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
    (S2934CorrectedT hQ D atBase generator_identification W I2892 I).arithmetic =
      S2847A6 :=
  rfl

#check S2934CorrectedT
#check S2934CorrectedT_source
#check S2934CorrectedT_arithmetic
#print axioms S2934CorrectedT
#print axioms S2934CorrectedT_source

end LeanFormal.IUT.XiFPaper.S2934CorrectedTFromCompletionActual
end
