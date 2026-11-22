import LeanFormal.IUT.Audit.Status

/-!
# S3137: final R1 state (task-53 report record)

Exact final state of the R1 same-C model-map residual after qpilot's minimal
Gaussian model map (all declarations EXIT0 + fresh olean + trio probes):

* M0 PROVED: S3133GaussianModelMapResidualMinimal_m0
  (actual SourceCompletion above the concrete Gaussian arithmetic; IUT I
  Definition 3.1).
* M3 PROVED: S3133GaussianModelMapResidualMinimal_m3
  (actual Gaussian Stage-2 image theta values match the source theater;
  IUT II Remark 2.5.1(i)).
* Residual M1: R.m1_indexInjection : Prop in
  S3133GaussianModelMapResidualMinimal D — the bad <-> all-place index
  injection (shape S3133BadToAllPlaceIndexInjectionData); genuine source
  placeToMod provenance missing (contract-separated; no record projection).
  Page refs: IUT I Definition 3.1(b),(e); IUT III Proposition 3.4(ii).
* Residual shrunk M2: R.m2_baseQMatch : Prop with
  m2_baseQMatch_eq : m2_baseQMatch = S3133GaussianQParameterMatchAtBase
  C.toSourceNativeInitialThetaData, i.e. at every bad place whose rational
  prime is 5, the clause-B q has completion norm 1/5; otherwise the base-q
  descent F -> Fmod is the genuine source missing datum.
  Page refs: IUT I Example 3.2(iv); IUT III Definition 3.8(i);
  IUT II Remark 2.5.1(i).
* Readout-side residual (task-40/task-28): M4 raw Remark 3.1.1(ii) weight
  total-one (normalized-weight alternative unconditional) and M5a/M5b
  canonical readout equalities (mainline S3131PaperRegionalQ/Hull readouts).

The exact residual identification is proved:
  GaussianR1ReducedResidual ↔ (R.m1_indexInjection ∧ R.m2_baseQMatch)
(S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff),
with M0/M3 filled from the qpilot proofs and the readout side handled by the
green S3137 comparison-consumer chain.

Registry: canonical id R1.M2M3M5.sameC-q-theta-readout
(S3137R1RegistryCanonicalActual.S3137R1RegistryCanonical).  No carrier
substitution, no sorry, no axiom.  WRITE-ONLY.
-/

namespace LeanFormal.IUT.Audit

/-- Final R1 state: proved fields, exact residual M1/M2 types and page refs,
readout-side residual, and the canonical registry id. -/
def S3137R1FinalState : Obligation :=
  { id := "S3137.state.R1-final"
    source := "IUT I Def 3.1(b),(e), Ex 3.2(iv); IUT II Rem 2.5.1(i); IUT III Prop 3.4(ii) pp.102-103; Def 3.8(i) p.112; Prop 3.9(i) p.115; Remark 3.1.1(ii); IUT IV Prop 1.4(i); Cor 3.12"
    status := VerificationStatus.pending
    note := "M0/M3 proved (qpilot m0/m3).  Residual M1 = m1_indexInjection (bad<->all-place injection; source placeToMod provenance missing; I Def 3.1(b),(e); III Prop 3.4(ii)); shrunken M2 = m2_baseQMatch (clause-B base-q descent + Gaussian norm 1/5 above 5; I Ex 3.2(iv); III Def 3.8(i)); readout M4/M5 task-40.  Exact iff theorem gaussianR1ReducedResidual_residual_iff.  Canonical registry id R1.M2M3M5.sameC-q-theta-readout."
    dependsOn := ["S3133S3131GaussianModelMapMinimalActual", "S3137GaussianR1ResidualLightActual", "S3137SameCModelMapResidualActual", "S3137R1RegistryCanonicalActual"] }

end LeanFormal.IUT.Audit
