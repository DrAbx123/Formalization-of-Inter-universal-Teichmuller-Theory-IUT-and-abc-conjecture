import LeanFormal.IUT.Audit.Status

/-! # S3278: S6 Mzk1BetaAvoidingBelyiSmall audited — partial cases PROVED; named blocker remains

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

def S3278S6Audit : List (String × String × String) := [
  ("checker+probe", "PASS", "Mzk1BetaAvoidingBelyiSmallActual CITABLE 34 decls 36171B sha 2F326056603B15D4...; checker WITH _S3278S6Probe: probe_ok TRUE; last_exit 0; olean 1407400B sha 7C261506F957674A...; axioms trio only"),
  ("PROVED cases", "THEOREMS", "exists_belyi_betaAvoiding_card_le_two (#S<=2 full); exists_belyi_betaAvoiding_three_of_lt (#S=3, beta strictly between min/max); exists_belyi_three_of_gt_of_odd + exists_belyi_three_of_lt_of_odd (exterior parity cases, positive-slope construction + sign of B at u>1/u<0); canonical_exterior_bad_point (B(1,2)(4/3)=1 counterexample to canonical one-layer); exists_belyi_betaAvoiding_example_exterior (two-layer workaround example); belyiPolynomial_critIn01 + critIn01_of_criticalValues_subset + criticalValues_comp_subset_zero_one + affineNorm + eval bounds"),
  ("NAMED remaining", "BelyiBetaAvoidingExteriorStatement", "exact remaining statement for #S=3 with beta outside convex hull (parity residue; canonical one-layer construction fails exactly at extra preimages of 1); blocker documented in 6-row ledger; NOT proved"),
  ("scope", "NOT closure", "S6 = |S|<=3 small-case progress only; general rational beta-avoiding step (BetaAvoidingStep) remains NAMED; full-Qbar named; paper closure NOT claimed"),
  ("recommended V150 supplement", "SMALL IN-PLACE (beta row)", "beta row = 'S6 |S|<=3: #S<=2 full PROVED + #S=3 interior PROVED + exterior parity partial + named blocker BelyiBetaAvoidingExteriorStatement (canonical one-layer fails at extra preimages of 1; two-layer example proved)'; no closure"),
  ("verdict", "S6 AUDITED (partial cases PROVED; named blocker)", "counts as progress evidence only; gate NOT PASSED; binding HOLD") ]

theorem S3278S6Audit_length : S3278S6Audit.length = 6 := rfl

def S3278S6AuditRecord : Obligation :=
  { id := "IUT.project.s6-small-audit"
    source := "Lead A366 follow-up 2026-11-10 22:21; checker+probe"
    status := VerificationStatus.interface
    note := "S6 AUDITED: Mzk1BetaAvoidingBelyiSmall CITABLE 34 decls 36171B 2F326056 probe_ok (olean 1407400 7C261506) — PROVED: #S<=2 full; #S=3 interior; exterior parity odd cases; canonical_exterior_bad_point; example_exterior; C-point CV bridge/composition/affineNorm; NAMED blocker BelyiBetaAvoidingExteriorStatement (parity residue, canonical one-layer fails at extra preimages of 1) remains. Small in-place V150 supplement recommended (beta row: proved cases + named blocker; no closure). GATE NOT PASSED; binding HOLD."
    dependsOn := [ "S3277V151SpotCheckRecord" ] }

#check S3278S6AuditRecord
#check S3278S6Audit_length

end LeanFormal.IUT.Audit
