import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S2870A6CFPathAudit

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2854SignQuotientAudit
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2891A6CFActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- The A6 cF obtained from the pointwise stack Q once IsStack is supplied. -/
noncomputable def S2891CF
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K)) :
    Iut.HyperbolicOrbicurve S2847A6.F :=
  S2870CF S2882A6Q hQ

/-- A6 stack quotient input, conditional only on IsStack plus quotient/witness. -/
noncomputable def S2891Input
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K))
    (A : Iut.OrbicurveSignAction
      S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (W : S2870QuotientWitnessData S2882A6Q hQ A) :
    S2854StackQuotientInput
      S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve A :=
  S2870Input S2882A6Q hQ A W

#check S2891CF
#check S2891Input

end LeanFormal.IUT.XiFPaper.S2891A6CFActual
end
