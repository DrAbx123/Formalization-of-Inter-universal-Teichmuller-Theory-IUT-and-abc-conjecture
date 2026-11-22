import LeanFormal.IUT.Audit.Status

/-! # S3271: SECOND SPEC REPAIR — BadParam targets REFUTED; corrected sharp theorems PROVED (+ bridge/reduction audits)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

def S3271Audit : List (String × String × String) := [
  ("BadParam checker+probe", "PASS", "Mzk1BadParamProofActual CITABLE 35 decls 18633B sha E6E18A440D0F7FC1...; checker WITH _Mzk1BadParamProofProbeActual: probe_ok TRUE; last_exit 0; axioms trio only"),
  ("scaling law PROVED", "THEOREM", "belyiConst_scaling (c_{kp,kq} = (c_{p,q})^k) + belyiEvalQ_scaling (B_{kp,kq}(u) = (B_{p,q}(u))^k) — kernel-checked"),
  ("ORIGINAL TARGETS REFUTED", "KERNEL-CHECKED DISPROOF (no error)", "not_badParamSet_finite (p=q=1,u=1/2: badParamSet = Set.univ, infinite; via badParamSet_one_one_half + Set.infinite_univ); not_exists_good_param (forall k B(1,1)(1/2)=1 via belyiEvalQ_one_one_half_eq_one => contradiction); not_collision_finite_statement (collision analog false: B(1,1)=4X(1-X) symmetric, u=1/4 vs 3/4)"),
  ("corrected SHARP theorems PROVED", "THEOREMS", "badParamSet_finite_iff (finite iff B != 1 and B != -1); badParamSet_finite_of_ne; exists_good_param_of_ne_one (k=1 good when B != 1); badParamSet_finite_corrected/exists_good_param_corrected PROVED; collisionParamSet_finite_iff/'"),
  ("implication", "HONEST CORRECTION", "second false-target repair after S3268; original badparam plan premise wrong; beta-avoiding step must avoid critical point/equal B-values or renormalize; BetaAvoidingStep REMAINS NAMED; accounted in FINAL ROWS (d) row"),
  ("PolyEvalP1Bridge", "PASS", "Mzk1PolyEvalP1Bridge CITABLE 38 decls 22692B sha 1A8272C1D6D80B17...; probe _Mzk1PolyEvalP1BridgeProbeActual: probe_ok TRUE (one-off #4: polyEvalP1_ofFinite/infty/eq_polyMapPoints, specialSet_eq_polyMapSpecialSet, mapRatComplex injective/specialSet iffs, polyEvalP1C variants)"),
  ("BetaAvoidingReduction", "PASS (STATEMENT ONLY)", "Mzk1BetaAvoidingReduction CITABLE 3 decls 2914B sha E94D7E39...; probe _S3271ReductionProbe: probe_ok TRUE — BetaAvoidingReductionStatement named class-B (exact parametric reduction; 5-row ledger; blocker documented: TauCeti construction collision with B=1 branch; maximizer uniqueness/explicit (m,n) choice not in tree); NOT proved"),
  ("verdict", "SECOND SPEC REPAIR AUDITED + bridge/reduction", "no closure claim; BetaAvoidingStep named remains; GATE NOT PASSED; binding HOLD") ]

theorem S3271Audit_length : S3271Audit.length = 8 := rfl

def S3271AuditRecord : Obligation :=
  { id := "IUT.project.badparam-spec-repair-audit"
    source := "Lead/lattice A349/A350 2026-11-10 21:58; checker+probe"
    status := VerificationStatus.interface
    note := "SECOND SPEC REPAIR AUDITED: Mzk1BadParamProof CITABLE 35 decls 18633B probe_ok — scaling c_{kp,kq}=(c_{p,q})^k / B_{kp,kq}=(B_{p,q})^k PROVED; original badParamSet_finite and exists_good_param KERNEL-CHECKED REFUTED (p=q=1,u=1/2 => badParamSet=univ; all k B=1); naive collision statement also false (symmetry u=1/4 vs 3/4); corrected sharp PROVED: badParamSet_finite_iff (finite iff B != 1,-1), badParamSet_finite_of_ne, exists_good_param_of_ne_one, corrected props. BetaAvoidingStep stays NAMED; premise correction recorded in FINAL ROWS (d). ALSO: PolyEvalP1Bridge CITABLE 38/22692 1A8272C1 probe_ok (one-off #4); BetaAvoidingReduction CITABLE 3/2914 E94D7E39 probe_ok but STATEMENT ONLY (named class-B; blocker documented)."
    dependsOn := [ "S3270AuditRecord", "S3269S7AuditRecord" ] }

#check S3271AuditRecord
#check S3271Audit_length

end LeanFormal.IUT.Audit
