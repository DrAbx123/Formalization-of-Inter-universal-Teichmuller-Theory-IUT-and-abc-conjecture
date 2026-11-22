import tmp.sheaf.xif.paper.S2104D9HonestQuotientActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2104D9HonestQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2854SignQuotientAux

/-- Exact stack-quotient input for cF/quotient/quotientWitness over an
arbitrary hyperbolic orbicurve and sign action. -/
structure S2854StackQuotientInput
    {F : Type*} [Field F]
    (xF : Iut.HyperbolicOrbicurve F)
    (signAction : Iut.OrbicurveSignAction xF) where
  cF : Iut.HyperbolicOrbicurve F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient

/-- Abstract A6 sign-quotient gap, avoiding the unavailable S2851 term. -/
def S2854A6StackQuotientGap
    {F : Type*} [Field F]
    (xF : Iut.HyperbolicOrbicurve F)
    (signAction : Iut.OrbicurveSignAction xF) : Prop :=
  Nonempty (S2854StackQuotientInput xF signAction)

/-! S2104 provider is only for the S1726 curve; exact interface shape. -/
#check S2104CFOfStackWitness
#check S2104QuotientOfStackWitness
#check S2104WitnessOfStackWitness
#check S2104HonestCFQuotientOfStackWitness

#print axioms S2104CFOfStackWitness
#print axioms S2104QuotientOfStackWitness
#print axioms S2104WitnessOfStackWitness
#print axioms S2104HonestCFQuotientOfStackWitness

end LeanFormal.IUT.XiFPaper.S2854SignQuotientAux
end