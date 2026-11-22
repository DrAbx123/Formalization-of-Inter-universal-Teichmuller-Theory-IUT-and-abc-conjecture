import tmp.sheaf.xif.paper.S3136LGPRealifiedValueTransportActual
import tmp.sheaf.xif.paper.S3136LGPQVPilotPrincipalIdealActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual

/-! # Stage-4 host: weight-agreement bridge to the bad<->C3 model-map interface

Source anchors: IUT II, Remark 2.5.1, (i) (theta values / q_v parameters);
IUT III, Def. 3.8, (i) (p. 112-113) and Remark 3.9.4 (realified log-volume
normalization); IUT III, Prop. 3.7, (i) (pp. 108-109).

This file bridges the actual LGP theta divisor weights to the bad-place/qpilot
model-map interface:
* lgpBadWeight b = the actual q_v divisor exponent ord_v(q_v) as a real number;
* lgpBadRealifiedLogValue b = its multiplicative-real realification;
* lgpBadRealifiedLogValue_eq: this realified value is exactly the LGP realified
  value of the actual q_v principal prime divisor (bridge to the previous
  batches);
* lgpBadWeight_pos: the actual bad-place weight is positive;
* lgpBadWeight_degreeFaithful: qpilot's actual degree-faithfulness criterion
  (globalRealifiedPrimePowerHom_degree_faithful) instantiated with the actual
  LGP bad weight as the arithmetic weight;
* LGPWeightAgreementMissing/Gap: exact missing data (bad-to-global-prime map,
  weight agreement with qpilot's globalPrimeWeight, normalization; refs above),
  with the qpilot M0/M2/R1 residual interface exposed for consumers.

LABEL: prerequisite component only.  Consumer: lattice stream (R1/R-A/R-C),
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
open LeanFormal.IUT.XiFPaper.S3136FrobenioidIsoLayerActual
open LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual
open LeanFormal.IUT.XiFPaper.S3136LGPQVPilotPrincipalIdealActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalFractionalIdealCandidate
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual bad-place weight: the q_v divisor exponent ord_v(q_v) as a real
number. -/
def lgpBadWeight (b : Bad (nativePlaceSelection T)) : ℝ :=
  ((lgpQVDivisorExponent T b : ℕ) : ℝ)

/-- The realified log value of the actual bad-place weight. -/
noncomputable def lgpBadRealifiedLogValue (b : Bad (nativePlaceSelection T)) :
    Multiplicative ℝ :=
  Multiplicative.ofAdd (lgpBadWeight T b)

/-- The actual bad-place realified value is the LGP realified value of the q_v
principal prime divisor. -/
theorem lgpBadRealifiedLogValue_eq (b : Bad (nativePlaceSelection T)) :
    lgpBadRealifiedLogValue T b =
      lgpRealifiedLogValue T
        (Algebra.GrothendieckAddGroup.of (lgpQVPilotPrimeDivisor T b)) := by
  unfold lgpBadRealifiedLogValue lgpBadWeight
  have hexp : lgpThetaDivisorExponent T (b, lgpThetaLabelOne l) =
      lgpQVDivisorExponent T b := by
    have h1 : lgpThetaDivisorExponent T (b, lgpThetaLabelOne l) =
        lgpThetaDivisorTotalExponent T
          (lgpThetaPilotPrimeDivisor T (b, lgpThetaLabelOne l)) :=
      (lgpThetaDivisorTotalExponent_single T (b, lgpThetaLabelOne l)).symm
    rw [h1]
    exact lgpQVPilotPrimeDivisor_total T b
  rw [lgpQVPilotPrimeDivisor, lgpRealifiedLogValue_of_single, hexp]

/-- The actual bad-place weight is positive. -/
theorem lgpBadWeight_pos (b : Bad (nativePlaceSelection T)) :
    0 < lgpBadWeight T b := by
  unfold lgpBadWeight
  have hexp : lgpThetaDivisorExponent T (b, lgpThetaLabelOne l) =
      lgpQVDivisorExponent T b := by
    have h1 : lgpThetaDivisorExponent T (b, lgpThetaLabelOne l) =
        lgpThetaDivisorTotalExponent T
          (lgpThetaPilotPrimeDivisor T (b, lgpThetaLabelOne l)) :=
      (lgpThetaDivisorTotalExponent_single T (b, lgpThetaLabelOne l)).symm
    rw [h1]
    exact lgpQVPilotPrimeDivisor_total T b
  have hpos : 0 < lgpThetaDivisorExponent T (b, lgpThetaLabelOne l) :=
    lgpThetaDivisorExponent_pos T (b, lgpThetaLabelOne l)
  rw [hexp] at hpos
  exact_mod_cast hpos

/-- Qpilot's actual degree-faithfulness criterion instantiated with the actual
LGP bad weight as the arithmetic weight: for a nonzero bad weight, the
realified generator is degree-faithful. -/
theorem lgpBadWeight_degreeFaithful
    {X : N8NativeInput l} (v : GlobalPrimeIndex (X := X))
    (b : Bad (nativePlaceSelection T))
    (hweight : globalPrimeWeight (X := X) v = lgpBadWeight T b)
    (r s : Multiplicative ℝ)
    (h : globalDegree (X := X) (globalRealifiedPrimePowerHom X v r) =
      globalDegree (X := X) (globalRealifiedPrimePowerHom X v s)) :
    r = s := by
  apply globalRealifiedPrimePowerHom_degree_faithful (X := X) v _ r s h
  rw [hweight]
  exact ne_of_gt (lgpBadWeight_pos T b)

/-- Exact missing data for the weight-agreement bridge (IUT II, Remark 2.5.1,
(i); IUT III, Def. 3.8, (i); Remark 3.9.4; Prop. 3.7, (i), (ii)):
* badToGlobalPrime: the actual identification of the bad places with qpilot's
  global prime index (the bad<->all-place injection plus M0 place transport);
* weightAgreement: agreement of qpilot's actual arithmetic weight with the
  actual LGP bad weight lgpBadWeight;
* normalizationCompatibility: compatibility of the realified log-volume
  normalization with the paper's (Remark 3.9.4);
* r1Residual: the qpilot M0/M2/R1 residual interface (m1 index injection and
  shrunk m2 base-q match) that supplies the index/place comparison. -/
structure LGPWeightAgreementMissing where
  badToGlobalPrime : Prop
  weightAgreement : Prop
  normalizationCompatibility : Prop
  r1Residual : Prop

/-- The exact weight-agreement gap. -/
def LGPWeightAgreementGap : Prop := Nonempty LGPWeightAgreementMissing

#check lgpBadWeight
#check lgpBadRealifiedLogValue_eq
#check lgpBadWeight_pos
#check lgpBadWeight_degreeFaithful
#check LGPWeightAgreementGap
#check S3137R1_interface

end LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual
end