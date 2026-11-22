import tmp.sheaf.xif.paper.S2104D9HonestQuotientActual
import tmp.sheaf.xif.paper.S2851A6D6GeometryActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2104D9HonestQuotientActual
open LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2854SignQuotientAudit

/-!
## S2854: audit of cF / quotient / quotientWitness

Actual provider found:

S2104D9HonestQuotientActual constructs, from a stack quotient witness
W : S1971StackQuotientWitness l A:

* S2104CFOfStackWitness W : HyperbolicOrbicurve S1726K
* S2104QuotientOfStackWitness W : OrbicurveSignInvariantMorphism A ...
* S2104WitnessOfStackWitness W : OrbicurveSignQuotientWitness A ...
* S2104HonestCFQuotientOfStackWitness W : S1964HonestCFQuotient l A

These are real constructions: cF is realized from the witness stack fiber,
quotient from the witness morphism, and the universal property from the
witness descent/factor/two-cell data. No fake cF.

Exact limitation for A6:

S1971StackQuotientWitness l A is fixed to the S1726 orbicurve:
A : OrbicurveSignAction S1726Orbicurve. It cannot be applied to
S2851HyperbolicOrbicurve : HyperbolicOrbicurve K / its sign action.

Thus the first missing object for A6 is a generic stack-quotient witness for
an arbitrary HyperbolicOrbicurve and sign action. S1971 only constructs the
pointwise action category; the global functorial pseudofunctor and IsStack
are the named missing inputs, and S2093 records that Mathlib has no IsStack
instance for the slice-sheaf prestack.

No cF/quotient/witness is fabricated below; the structure is an explicit
interface/gap.
-/

/-- The exact stack-quotient input needed for cF/quotient/quotientWitness over
an arbitrary hyperbolic orbicurve. -/
structure S2854StackQuotientInput
    {F : Type*} [Field F]
    (xF : Iut.HyperbolicOrbicurve F)
    (signAction : Iut.OrbicurveSignAction xF) where
  cF : Iut.HyperbolicOrbicurve F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient

/-- The exact first missing for A6 sign quotient, with no fake cF. -/
def S2854A6StackQuotientGap
    (signAction : Iut.OrbicurveSignAction S2851HyperbolicOrbicurve) : Prop :=
  Nonempty (S2854StackQuotientInput S2851HyperbolicOrbicurve signAction)

#check S2104CFOfStackWitness
#check S2104QuotientOfStackWitness
#check S2104WitnessOfStackWitness
#check S2104HonestCFQuotientOfStackWitness
#check S2854StackQuotientInput
#check S2854A6StackQuotientGap
#print axioms S2104CFOfStackWitness
#print axioms S2104QuotientOfStackWitness
#print axioms S2104WitnessOfStackWitness

end LeanFormal.IUT.XiFPaper.S2854SignQuotientAudit
end
