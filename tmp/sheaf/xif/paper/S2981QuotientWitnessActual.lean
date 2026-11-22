import tmp.sheaf.xif.paper.S2980QuotientMorphismActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2979CFQuotientActual
open LeanFormal.IUT.XiFPaper.S2980QuotientMorphismActual
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

namespace LeanFormal.IUT.XiFPaper.S2981QuotientWitnessActual

noncomputable def S2981QuotientWitness
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K))
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (W : S2870QuotientWitnessData S2882A6Q hQ A) :
    Iut.OrbicurveSignQuotientWitness A (S2980Quotient hQ A W) :=
  (S2979CFQuotient hQ A W).quotientWitness

#check S2981QuotientWitness

end LeanFormal.IUT.XiFPaper.S2981QuotientWitnessActual
end
