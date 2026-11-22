import LeanFormal.IUT.Audit.Status

/-! # S3268: SPEC REPAIR audited — literal 0/1 CV target REFUTED; image-based invariant PROVED

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

def S3268SpecRepair : List (String × String × String) := [
  ("checker+probe", "PASS", "Mzk1CritValueInImageProofActual CITABLE 32 decls 22392B sha E96DAF7021EBA411...; checker WITH _Mzk1CritValueInImageProofProbeActual (474B): probe_ok TRUE; last_exit 0; zero sorryAx; axioms trio only"),
  ("literal 0/1 target REFUTED", "KERNEL-CHECKED REFUTATION (no error)", "s3135_critValueInImage_counterexample: for every D with Even n, exists z : C with gPoly'(z)=0 and gPoly(z) != 0 and != 1 (critPointZ; uses belyiNormConst_mul_aeval_gPoly_at_critPointZ + belyiNormConst_ne_one); s3135_critValueInImage_refuted : NOT (forall z, gPoly'(z)=0 -> gPoly(z)=0 or 1). Refutation verified correct (counterexample is third critical value (m^m n^n)/(m+n)^(m+n) != 1)"),
  ("image-based invariant PROVED", "THEOREM (real)", "critValueInImageStatement_proved : CritValueInImageStatement PROVED (C-point critical value equals gPoly at a rational source point; task item (i) now proved in image-based form)"),
  ("normalization fix PROVED", "THEOREM", "belyiNormGPoly_critValue_zero_or_one (belyiNormGPoly = normalized polynomial whose critical values lie in {0,1}); supporting belyiNormConst/gPoly_eq_belyi21_comp_add/aeval_derivative_gPoly_eq/aeval_belyi21/aeval_derivative_belyi21 etc"),
  ("spec repair record", "HONEST REPAIR", "requested literal 0/1 target is FALSE for unnormalized gPoly; replaced by (a) image-based CritValueInImageStatement PROVED, or (b) normalized belyiNormGPoly_critValue_zero_or_one PROVED; critValueInImageSpecBlocker documents this; 7-row ledger"),
  ("verdict", "SPEC REPAIR PASS — literal target refuted; image-based invariant proved", "record 'literal 0/1 target refuted by counterexample; image-based invariant proved' in S3178/FINAL ROWS; no closure claim for paper; GATE NOT PASSED; binding HOLD") ]

theorem S3268SpecRepair_length : S3268SpecRepair.length = 6 := rfl

def S3268SpecRepairRecord : Obligation :=
  { id := "IUT.project.critvalue-spec-repair"
    source := "Lead one-off #1 2026-11-10 21:46; checker+probe"
    status := VerificationStatus.interface
    note := "SPEC REPAIR AUDITED: Mzk1CritValueInImageProof CITABLE 32 decls 22392B probe_ok — (a) literal 0/1 target KERNEL-CHECKED REFUTED (counterexample at critPointZ: third critical value != 0,1; no refutation error); (b) critValueInImageStatement_proved (image-based C-point CV-in-image) PROVED; (c) belyiNormGPoly_critValue_zero_or_one (normalized fix) PROVED; axioms trio only; 7-row ledger. Record: 'literal 0/1 target refuted by counterexample; image-based invariant proved'. No closure; GATE NOT PASSED."
    dependsOn := [ "S3257AuditRecord" ] }

#check S3268SpecRepairRecord
#check S3268SpecRepair_length

end LeanFormal.IUT.Audit
