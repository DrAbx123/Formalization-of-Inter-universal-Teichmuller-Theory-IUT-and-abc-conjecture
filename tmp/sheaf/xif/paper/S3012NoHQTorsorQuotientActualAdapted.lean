import tmp.sheaf.xif.paper.S3011TorsorStackWitnessHelperActual
import tmp.sheaf.xif.paper.S2870A6CFPathAudit

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3011TorsorStackWitnessHelperActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

namespace LeanFormal.IUT.XiFPaper.S3012NoHQTorsorQuotientActualAdapted

/-- No-hQ torsor quotient data.  This is a CONDITIONAL interface: `cF`,
`quotient`, `quotientWitness` are explicit fields; it does not claim that
`hQ : S2882A6Q.IsStack ...` has been constructed. -/
structure S3012NoHQTorsorQuotientData
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve) where
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient

/-- Conditional bridge to S3011: only when `hQ` is supplied explicitly and
`cF` is identified with `S2891CF hQ`. -/
noncomputable def S3012NoHQTorsorQuotientData.toHQ
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (D : S3012NoHQTorsorQuotientData A)
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F))
    (hcf : D.cF = S2891CF hQ) :
    S3011TorsorQuotientData A hQ := by
  cases hcf
  exact ⟨D.quotient, D.quotientWitness⟩

/-- Conditional `toW`: only under the explicit `hQ`/`hcf` hypotheses. -/
noncomputable def S3012NoHQTorsorQuotientData.toW
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (D : S3012NoHQTorsorQuotientData A)
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F))
    (hcf : D.cF = S2891CF hQ) :
    S2870QuotientWitnessData S2882A6Q hQ A :=
  (D.toHQ hQ hcf).toW

#check S3012NoHQTorsorQuotientData
#check S3012NoHQTorsorQuotientData.toHQ
#check S3012NoHQTorsorQuotientData.toW
#print axioms S3012NoHQTorsorQuotientData.toHQ
#print axioms S3012NoHQTorsorQuotientData.toW

end LeanFormal.IUT.XiFPaper.S3012NoHQTorsorQuotientActualAdapted
end
