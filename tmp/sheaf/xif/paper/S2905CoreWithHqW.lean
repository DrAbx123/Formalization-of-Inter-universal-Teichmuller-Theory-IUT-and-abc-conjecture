import tmp.sheaf.xif.paper.S2892CoreWithQActual
import tmp.sheaf.xif.paper.S2887CorrectedCoreMinimalActual
import tmp.sheaf.xif.paper.S2869A6CoreWithGenericQuotient
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2892CoreWithQActual
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
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

namespace LeanFormal.IUT.XiFPaper.S2905CoreWithHqW

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Final corrected A6 core from IsStack Q plus quotient witness, with all
remaining inputs explicit. -/
noncomputable def S2905Core
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
    SourceSignQuotientDataCorrected S2847A6 :=
  S2892Core hQ D atBase generator_identification W I

/-- Compatibility: S2905Core is S2892Core with all inputs named explicitly. -/
theorem S2905Core_eq
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
    S2905Core hQ D atBase generator_identification W I =
      S2892Core hQ D atBase generator_identification W I := rfl

#check S2905Core
#check S2905Core_eq

end LeanFormal.IUT.XiFPaper.S2905CoreWithHqW
end
