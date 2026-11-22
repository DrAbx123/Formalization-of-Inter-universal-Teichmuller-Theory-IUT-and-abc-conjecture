import LeanFormal.IUT.Audit.Status

/-! # S3280: V150 v152 (S6 supplement) + v153 (consumer row) SPOT-CHECK PASS — final pin

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

def S3280V152V153SpotCheck : List (String × String × String) := [
  ("final pin (v153)", "PASS", "IUTExternal35GateV150Actual: EXIT=0 SIZE 12275B; src sha FEE211618195E64B67D272BBFAEA895F5DAE122583F7727FBBC64D0ECBBAFEAF; olean 271096B sha 62FDD56F844766FF03EBAD6E3383F4CCEF0874C5BD76498532A08C0738C44D12; checker WITH IUTExternal35GateProbeV150 CITABLE 2 decls probe_ok TRUE; supersedes v151 10550/C266ED6D and mainline's intermediate v152 11599/C8E218BF (v153 row added after)"),
  ("v152 S6 supplement row", "PASS", "'S6 small-case supplement (v152)': Mzk1BetaAvoidingBelyiSmallActual CITABLE 34 decls 36171B sha 2F326056603B15D4 probe_ok (olean 1407400 7C261506); |S|<=2 fully PROVED; interior |S|=3 fully PROVED; exterior parity partial PROVED; canonical_exterior_bad_point B_{1,2}(4/3)=1; example_exterior; REMAINING NAMED BelyiBetaAvoidingExteriorStatement proved:=false; general BetaAvoidingStep NAMED; full-Qbar named"),
  ("v153 consumer row", "PASS", "'DELIVERED consumer (F=Q rational scope; v153)': Mzk1Thm25P1CompositeConsumerActual CITABLE 12 decls 9619B (EXIT0; mainline verified): p1CompositeRealConsumerTarget_rational PROVED + p1Composite_mapPoints_consumer_rational PROVED; F=Q component RATIONAL SCOPE ONLY; full-Qbar consumer NOT wired; binding HOLD remains; no closure"),
  ("UNCHANGED checks", "PASS", "coverage line verbatim unchanged; 6 named inputs proved:=false unchanged (rows 1-6); HOLD row unchanged (Thm25Unconditional off-queue; no un-HOLD/no queue); L8 FROZEN; GATE-VERDICT = GATE NOT PASSED with S6 v152 + consumer v153 noted, no Thm2.5/paper2.4/abc closure; header documents v152 approved Lead A368 (after S3278) and v153 approved Lead A370 (mainline verified); pins 14041/record 18800; no registry edits"),
  ("verdict", "SPOT-CHECK PASS (v152+v153)", "canonical pin updated; gate NOT PASSED; binding HOLD; no un-HOLD") ]

theorem S3280V152V153SpotCheck_length : S3280V152V153SpotCheck.length = 5 := rfl

def S3280V152V153SpotCheckRecord : Obligation :=
  { id := "IUT.project.v152-v153-spot-check"
    source := "lattice V152/V153 edits (Lead A368/A370) 2026-11-10 22:25; checker+probe"
    status := VerificationStatus.interface
    note := "V152+V153 SPOT-CHECK PASS: IUTExternal35GateV150Actual EXIT0 12275B src FEE21161 olean 271096 62FDD56F; checker+probe CITABLE 2 probe_ok; v152 S6 supplement row (S6 proved cases + named BelyiBetaAvoidingExteriorStatement proved:=false) + v153 consumer row (Mzk1Thm25P1CompositeConsumer 12/9619 F=Q rational scope; full-Qbar not wired; HOLD) both present; coverage/named inputs/HOLD/L8/verdict unchanged (GATE NOT PASSED, no closure); supersedes v151 10550/C266ED6D and intermediate v152 11599/C8E218BF."
    dependsOn := [ "S3279ConsumerAuditRecord", "S3278S6AuditRecord" ] }

#check S3280V152V153SpotCheckRecord
#check S3280V152V153SpotCheck_length

end LeanFormal.IUT.Audit
