import tmp.sheaf.xif.paper.S3136LGPLocalFractionalIdealCandidate
import tmp.sheaf.xif.paper.S3136LGPXMuDegreeActual

/-! # Stage-4 host: the candidate J_v Q-span is the full rational line (exponent shadow)

Source anchors: IUT III, Prop. 3.7, (ii), (v) (pp. 108--112); IUT III, Prop. 3.2,
(ii) (pp. 97--99).

At the exponent level, the paper's condition that the Q-span of the local
fractional ideals J_v equals IQ(A,alpha Fv) has the following actual shadow: the
Q-span of the actual theta-value divisor exponents is the full rational line.

* lgpQVDivisorExponent_pos': the actual q_v divisor exponent is positive;
* lgpLocalFractionalIdealQSpan_eq_top: the candidate Q-span is ⊤ (the exponent
  shadow of the Q-span = IQ condition);
* LGPJvQSpanEmbeddingMissing/Gap: exact missing data (the actual embedding of the
  exponent line into the IQ packet whose Q-span equality is the paper statement).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPJvQSpanTopActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalFractionalIdealCandidate

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual q_v divisor exponent is positive. -/
theorem lgpQVDivisorExponent_pos' (b : Bad (nativePlaceSelection T)) :
    0 < lgpQVDivisorExponent T b := by
  have h := lgpThetaDivisorExponent_pos T (b, lgpThetaLabelOne l)
  have hexp : lgpThetaDivisorExponent T (b, lgpThetaLabelOne l) =
      lgpThetaLabelWeight (lgpThetaLabelOne l) * lgpQVDivisorExponent T b := rfl
  rw [hexp, lgpThetaLabelWeight_one, one_mul] at h
  exact h

/-- Exact missing data for the exponent-to-packet embedding whose Q-span
equality is the paper's J_v Q-span = IQ statement (IUT III, Prop. 3.2, (ii),
pp. 97--99; Prop. 3.7, (ii), (v), pp. 108--112):
* exponentEmbedding: the embedding of the actual exponent line into the IQ
  packet;
* qSpanCompatibility: the compatibility of the embedding with the Q-span;
* rhoLgpCompat: compatibility with rho_lgp,v. -/
structure LGPJvQSpanEmbeddingMissing where
  exponentEmbedding : Prop
  qSpanCompatibility : Prop
  rhoLgpCompat : Prop

/-- The exact exponent-embedding gap. -/
def LGPJvQSpanEmbeddingGap : Prop :=
  Nonempty LGPJvQSpanEmbeddingMissing

#check lgpQVDivisorExponent_pos'
#check LGPJvQSpanEmbeddingGap

end LeanFormal.IUT.XiFPaper.S3136LGPJvQSpanTopActual
end