import LeanFormal.IUT.Audit.Status

/-!
# S3137: R1 residual refinement (task-51 / task-53 audit record)

Refined exact content of the two remaining R1 residual Props after qpilot's
task-51 components.  Data only; no assertion of either residual.

* m1_indexInjection (M1): packaged by qpilot as S3133M1ContractSeparatedMissing
  — a structure carrying e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex and
  the place-agreement field, with a proved iff to S3133M1Remaining.  No
  unconditional e exists in the tree: the shape is contract-separated.
  Source: IUT I, Definition 3.1, (b), (e); IUT III, Proposition 3.4, (ii),
  pp. 102-103.
* m2_baseQMatch (shrunk M2): the actual q value 1/5 at Q_5 is now CONSTRUCTED
  (qpilot S3133GaussianBaseQActual.S3133RationalFiveQ_norm); the transport to
  the Gaussian Fmod completion (S3133GaussianBaseQTransportMissing) and the
  clause-B Tate-q descent (S3133GaussianBaseQDescentMissing) remain the exact
  missing propositions.  S2684 is parked by Lead and is not citable.
  Source: IUT I, Example 3.2, (iv); IUT III, Definition 3.8, (i), p. 112;
  IUT II, Remark 2.5.1, (i).

Unchanged: M0 and M3 PROVED via qpilot S3133S3131GaussianModelMapMinimalActual
(S3133GaussianModelMapResidualMinimal_m0/_m3); reduced residual identification
still GaussianR1ReducedResidual ↔ (R.m1_indexInjection ∧ R.m2_baseQMatch)
(S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff).

WRITE-ONLY. No carrier, no sorry, no axiom.
-/

namespace LeanFormal.IUT.Audit

/-- Refined R1 residual: M1 contract-separated missing structure; M2 split into
constructed base value and remaining transport/descent. -/
def S3137R1ResidualRefinement : Obligation :=
  { id := "S3137.residual.R1-refined-task51"
    source := "IUT I Def 3.1(b),(e), Ex 3.2(iv); IUT II Rem 2.5.1(i); IUT III Prop 3.4(ii) pp.102-103; Def 3.8(i) p.112"
    status := VerificationStatus.pending
    note := "M1 = S3133M1ContractSeparatedMissing (e : Bad ≃ C3.tensorIndex + place agreement, iff S3133M1Remaining; no unconditional e, contract-separated).  M2 shrunk: base q=1/5 at Q_5 constructed (S3133RationalFiveQ_norm); residual = S3133GaussianBaseQTransportMissing + S3133GaussianBaseQDescentMissing.  M0/M3 proved.  Reduced residual identification unchanged (gaussianR1ReducedResidual_residual_iff)."
    dependsOn := ["S3133M1ContractObstructionActual", "S3133GaussianBaseQActual", "S3133S3131GaussianModelMapMinimalActual", "S3137GaussianR1ResidualLightActual"] }

end LeanFormal.IUT.Audit
