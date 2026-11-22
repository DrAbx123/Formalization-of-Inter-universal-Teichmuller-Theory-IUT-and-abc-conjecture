import tmp.sheaf.xif.paper.S2981QuotientWitnessActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2981QuotientWitnessActual
open LeanFormal.IUT.XiFPaper.S2980QuotientMorphismActual
open LeanFormal.IUT.XiFPaper.S2979CFQuotientActual
open LeanFormal.IUT.XiFPaper.S2854SignQuotientAudit
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

namespace LeanFormal.IUT.XiFPaper.S2982WInputActual

/-- Explicit W input for the corrected A6 quotient: IsStack on the pointwise
prestack plus the quotient witness.  D itself is a separate explicit input;
no stackification is claimed here. -/
structure S2982WInput
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K))
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve) where
  W : S2870QuotientWitnessData S2882A6Q hQ A

noncomputable def S2982WInput.quotient
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K)}
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2982WInput hQ A) :
    Iut.OrbicurveSignInvariantMorphism A (S2891CF hQ) :=
  (S2980Quotient hQ A I.W)

noncomputable def S2982WInput.quotientWitness
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K)}
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2982WInput hQ A) :
    Iut.OrbicurveSignQuotientWitness A (S2982WInput.quotient I) :=
  (S2981QuotientWitness hQ A I.W)

noncomputable def S2982WInput.toS2979
    {hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K)}
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2982WInput hQ A) :
    S2854StackQuotientInput S2855HyperbolicOrbicurve A :=
  S2979CFQuotient hQ A I.W

#check S2982WInput
#check S2982WInput.quotient
#check S2982WInput.quotientWitness
#check S2982WInput.toS2979

end LeanFormal.IUT.XiFPaper.S2982WInputActual
end
