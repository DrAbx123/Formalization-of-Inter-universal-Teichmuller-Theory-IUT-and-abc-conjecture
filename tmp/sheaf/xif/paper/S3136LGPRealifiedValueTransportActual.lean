import tmp.sheaf.xif.paper.S3133ValueGroupDegreeActual
import tmp.sheaf.xif.paper.S3136FrobenioidIsoLayerActual

/-! # Stage-4 host: realified value transport from qpilot's realified degree to the LGP cone

Source anchors: IUT III, Prop. 3.7, (i), (ii) (pp. 108--109) and IUT III,
Remark 3.9.4 / Prop. 3.9, (i), p. 115 (realified log-volume compatibility);
IUT II, Cor. 4.8, (ii).

This file constructs the REALIFIED VALUE TRANSPORT candidate between qpilot's
actual realified global degree data and the actual LGP theta divisor degree:
* lgpRealifiedLogValue: the multiplicative-real realification of the actual LGP
  theta divisor degree (via the actual Grothendieck comparison and degree hom);
* lgpRealifiedLogValue_of_single: its value on an actual LGP prime divisor is
  ofAdd of the actual theta divisor exponent;
* lgpRealifiedValueTransport_compat: conditional degree compatibility: for a
  qpilot global prime v and an LGP prime index p with agreeing arithmetic
  weight, the actual globalDegree of the realified prime power [v]^1 equals the
  LGP realified log value of the LGP prime divisor;
* LGPRealifiedValueTransportMissing/Gap: exact identification data to the
  paper's realified value transport (prime index identification, weight
  agreement, normalization/log-volume compatibility; refs above).

LABEL: prerequisite component only, NOT the paper's realified Frobenioid
isomorphism.  Consumer: lattice stream, IUT-III.theta-xmu-LGP-full-poly-
isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiLayerActual
open LeanFormal.IUT.XiFPaper.S3136FrobenioidIsoLayerActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The realified log value of an LGP divisor class: the multiplicative-real
realification of the actual LGP theta divisor degree. -/
noncomputable def lgpRealifiedLogValue
    (d : Algebra.GrothendieckAddGroup (LGPThetaDivisorCone (l := l) T)) :
    Multiplicative ℝ :=
  Multiplicative.ofAdd ((lgpRealifiedDegree T d : ℤ) : ℝ)

/-- Value on an actual LGP prime divisor: ofAdd of the actual theta divisor
exponent. -/
theorem lgpRealifiedLogValue_of_single
    (p : LGPPrimeIndex (l := l) T) :
    lgpRealifiedLogValue T
        (Algebra.GrothendieckAddGroup.of (lgpThetaPilotPrimeDivisor T p)) =
      Multiplicative.ofAdd ((lgpThetaDivisorExponent T p : ℕ) : ℝ) := by
  unfold lgpRealifiedLogValue
  rw [lgpRealifiedDegree_of, lgpThetaDivisorTotalExponent_single]
  simp

/-- Conditional degree compatibility: if qpilot's arithmetic weight of a global
prime v agrees with the actual LGP theta divisor exponent of an LGP prime index
p, then the realified global prime power [v]^1 and the LGP prime divisor have
the same realified degree. -/
theorem lgpRealifiedValueTransport_compat
    {X : N8NativeInput l} (v : GlobalPrimeIndex (X := X))
    (p : LGPPrimeIndex (l := l) T)
    (hweight : globalPrimeWeight (X := X) v =
      ((lgpThetaDivisorExponent T p : ℕ) : ℝ)) :
    globalDegree (X := X) (globalRealifiedPrimePower X v 1) =
      lgpRealifiedLogValue T
        (Algebra.GrothendieckAddGroup.of (lgpThetaPilotPrimeDivisor T p)) := by
  rw [globalDegree_realifiedPrimePower, lgpRealifiedLogValue_of_single, hweight]
  simp

/-- Exact identification data needed to identify the realified value transport
candidate with the paper's realified value transport (IUT III, Prop. 3.7, (i),
pp. 108--109; Remark 3.9.4 / Prop. 3.9, (i), p. 115; IUT II, Cor. 4.8, (ii)):
* primeIndexIdentification: the identification of the actual qpilot global
  prime index with the actual LGP prime index family (the bad<->C3 comparison
  plus the arithmetic-model place transport);
* weightAgreement: agreement of qpilot's actual arithmetic weight with the
  actual LGP theta divisor exponent;
* normalizationCompatibility: compatibility of the realified log-volume
  normalization with the paper's normalization (Remark 3.9.4);
* frobenioidIsoCompatibility: compatibility with the realified mod-to-MOD
  Frobenioid isomorphism. -/
structure LGPRealifiedValueTransportMissing where
  primeIndexIdentification : Prop
  weightAgreement : Prop
  normalizationCompatibility : Prop
  frobenioidIsoCompatibility : Prop

/-- The exact realified value transport gap. -/
def LGPRealifiedValueTransportGap : Prop :=
  Nonempty LGPRealifiedValueTransportMissing

#check lgpRealifiedLogValue
#check lgpRealifiedLogValue_of_single
#check lgpRealifiedValueTransport_compat
#check LGPRealifiedValueTransportGap

end LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual
end