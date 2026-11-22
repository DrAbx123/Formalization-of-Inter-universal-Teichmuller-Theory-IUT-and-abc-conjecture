import LeanFormal.IUT.Audit.Status

/-!
# S3137: R1 M2 subdivision (task-59 registry update, qpilot task-51)

Canonical record of the M2 split after qpilot's task-51 work.  M2 does NOT
disappear: the R1 residual is exactly M1 + M2a + M2b (plus readout M4/M5).

* M2a `INDEX.R1.M2.base-q-transport`: exact missing REFINED (task-60) to the
  base-field statement `S3133RationalFiveCompletionNorm : Prop` (exists nonzero
  x in the completion of Q at the five place with norm 5⁻¹;
  S3133M2aNormReductionActual EXIT0 144379), with `S3133GaussianCanonicalQNorm`
  as its Gaussian-completion consequence
  (`S3133GaussianCanonicalQNorm_of_rationalCompletionNorm`).  The earlier form was
  `S3133GaussianCanonicalQNorm : Prop` (canonical-completion q with norm 1/5;
  canonical-vs-normalized comparison, same class as
  `Example36CompletionNormFormulaActual.NormalizedLogNormComparison`).
  Constructed/proved: `S3133GaussianPadicCompletionHom` (actual Q_p -> Gaussian
  completion) and `S3133GaussianNormalizedTransport_norm_preserving`
  (S3133GaussianCompletionTransportActual); rational-side actual value
  `S3133RationalFiveQ_norm : ‖S3133RationalFiveQ‖ = 5⁻¹`
  (S3133GaussianBaseQRationalActual).  Ref: IUT I Ex 3.2(iv); III Def 3.8(i).
* M2b `INDEX.R1.M2.clause-B-descent`: exact missing declaration
  `S3133GaussianClauseBDescent (T) : Prop` (S3133GaussianM2MissingActual;
  clause-B/Tate q descent, D4).  Ref: IUT I Ex 3.2(iv); II Rem 2.5.1(i);
  III Def 3.8(i).
* Reduction: `S3133GaussianQParameterMatchAtBase_of_canonicalQ` (canonical q +
  per-b norm link => shrunk M2 atBase); task-60 additions:
  `S3133GaussianClauseBDescent_of_atBase` and
  `S3133GaussianQParameterMatchAtBase_of_ClauseBDescent_and_canonicalQ`
  (S3133M2bClauseBDescentActual EXIT0 144610), so M2a+M2b jointly equal the
  shrunk M2 atBase.  R1 residual count unchanged: M1 + M2a(base field) + M2b.

Data only; no residual asserted.  Not ABC-strength.  WRITE-ONLY.
-/

namespace LeanFormal.IUT.Audit

/-- M2 subdivision record for the mainline registry update. -/
def S3137M2Subdivision : Obligation :=
  { id := "S3137.registry.M2-subdivision"
    source := "IUT I, Example 3.2, (iv); IUT II, Remark 2.5.1, (i); IUT III, Definition 3.8, (i), p. 112"
    status := VerificationStatus.pending
    note := "M2a exact missing: S3133GaussianCanonicalQNorm : Prop (S3133GaussianM2MissingActual; transport hom + normalized norm preservation PROVED in S3133GaussianCompletionTransportActual; rational value S3133RationalFiveQ_norm).  M2b exact missing: S3133GaussianClauseBDescent (T) : Prop (S3133GaussianM2MissingActual).  R1 residual = M1 + M2a + M2b (+ readout M4/M5).  Reduction S3133GaussianQParameterMatchAtBase_of_canonicalQ.  NOT ABC-strength.  PARENT: R1.M2M3M5.sameC-q-theta-readout."
    dependsOn := ["R1.M2M3M5.sameC-q-theta-readout", "S3133GaussianM2MissingActual", "S3133GaussianCompletionTransportActual"] }

end LeanFormal.IUT.Audit