import tmp.sheaf.xif.paper.S2995A6StackWitnessSpec
import tmp.sheaf.xif.paper.S2996A6StackWitnessConstruction

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2995A6StackWitnessSpec
open LeanFormal.IUT.XiFPaper.S2996A6StackWitnessConstruction
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

namespace LeanFormal.IUT.XiFPaper.S3011TorsorStackWitnessHelperActual

/-- The torsor quotient data: the two S2995 fields that are not part of the
stack witness core. -/
structure S3011TorsorQuotientData
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)) where
  quotient : Iut.OrbicurveSignInvariantMorphism A (S2891CF hQ)
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient

noncomputable def S3011TorsorQuotientData.toW
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)}
    (D : S3011TorsorQuotientData A hQ) :
    S2870QuotientWitnessData S2882A6Q hQ A where
  quotient := D.quotient
  quotientWitness := D.quotientWitness

/-- Torsor stack witness: S2996 core + the torsor quotient data plus the
prestack/stackification fields. -/
structure S3011TorsorStackWitness
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)) where
  core : S2995A6StackWitnessCore
  torsor : S3011TorsorQuotientData A hQ
  prestack : Pseudofunctor.IsPrestack core.stack
    (Iut.SchemeOverField.etaleTopology S2994A6K)
  stackification : Pseudofunctor.IsStack core.stack
    (Iut.SchemeOverField.etaleTopology S2994A6K)

noncomputable def S3011TorsorStackWitness.toSpec
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)}
    (W : S3011TorsorStackWitness A hQ) :
    S2995A6StackWitnessSpec A where
  Q := W.core.stack
  isStack := W.stackification
  fiberEquiv := W.core.fiber_equiv
  hQ := hQ
  quotient := W.torsor.quotient
  quotientWitness := W.torsor.quotientWitness

noncomputable def S3011TorsorStackWitness.toW
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)}
    (W : S3011TorsorStackWitness A hQ) :
    S2870QuotientWitnessData S2882A6Q hQ A :=
  W.torsor.toW

#check S3011TorsorQuotientData
#check S3011TorsorQuotientData.toW
#check S3011TorsorStackWitness
#check S3011TorsorStackWitness.toSpec
#check S3011TorsorStackWitness.toW
#print axioms S3011TorsorStackWitness.toSpec
#print axioms S3011TorsorStackWitness.toW

end LeanFormal.IUT.XiFPaper.S3011TorsorStackWitnessHelperActual
end
