import tmp.sheaf.xif.paper.S3136LGPPhiInputSourceActual

/-! # Stage-4 host: theta divisor exponent compatibility restated for consumers

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT III, Prop. 3.7,
(ii), (v) (pp. 108--112).

This file restates, in a consumer-facing namespace, the actual factorization and
positivity of the LGP theta divisor exponents:
* lgpThetaDivisorExponent_factor: exponent = j^2-weight times ord_v(q_v);
* lgpThetaDivisorExponent_pos: positivity;
* lgpThetaPilotPrimeDivisor_nonzero: the pilot prime divisor is nonzero.

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaExponentCompatActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual LGP theta divisor exponent factorizes as j^2-weight times the
q_v divisor exponent. -/
theorem lgpThetaDivisorExponent_factor
    (p : LGPPrimeIndex (l := l) T) :
    lgpThetaDivisorExponent T p =
      lgpThetaLabelWeight p.2 * lgpQVDivisorExponent T p.1 :=
  rfl

/-- The actual LGP theta divisor exponent is positive. -/
theorem lgpThetaDivisorExponent_pos'
    (p : LGPPrimeIndex (l := l) T) :
    0 < lgpThetaDivisorExponent T p :=
  lgpThetaDivisorExponent_pos T p

/-- The actual LGP pilot prime divisor is nonzero. -/
theorem lgpThetaPilotPrimeDivisor_nonzero
    (p : LGPPrimeIndex (l := l) T) :
    lgpThetaPilotPrimeDivisor T p ≠ 0 :=
  lgpThetaPilotPrimeDivisor_ne_zero T p

#check lgpThetaDivisorExponent_factor
#check lgpThetaDivisorExponent_pos'
#check lgpThetaPilotPrimeDivisor_nonzero

end LeanFormal.IUT.XiFPaper.S3136LGPThetaExponentCompatActual
end