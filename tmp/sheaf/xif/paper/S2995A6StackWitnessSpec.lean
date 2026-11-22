import tmp.sheaf.xif.paper.S2993A6StackificationSpec
import tmp.sheaf.xif.paper.S2891A6CFActual
import tmp.sheaf.xif.paper.S2870A6CFPathAudit
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2993A6StackificationSpec
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

namespace LeanFormal.IUT.XiFPaper.S2995A6StackWitnessSpec

structure S2995A6StackWitnessSpec
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve) where
  Q : Iut.EtaleStackPseudofunctor S2994A6K
  isStack : Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)
  fiberEquiv :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (Q.obj U)
        (S2994A6PointwiseQuotient U))
  hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)
  quotient :
    Iut.OrbicurveSignInvariantMorphism A (S2891CF hQ)
  quotientWitness :
    Iut.OrbicurveSignQuotientWitness A quotient

noncomputable def S2995A6StackWitnessSpec.toW
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (S : S2995A6StackWitnessSpec A) :
    S2870QuotientWitnessData S2882A6Q S.hQ A where
  quotient := S.quotient
  quotientWitness := S.quotientWitness

#check S2995A6StackWitnessSpec
#check S2995A6StackWitnessSpec.toW

end LeanFormal.IUT.XiFPaper.S2995A6StackWitnessSpec
end
