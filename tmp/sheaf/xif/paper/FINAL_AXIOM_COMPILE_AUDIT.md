# Final paper-level axiom / compile audit

Date: 2026-10-29. Status: prepared, **not run yet**.

## Scope

Audit the paper-level xi-f targets and their actual-object dependencies after
the central compile queue reports EXIT 0. This script does not change any
mathematics.

## Files

- `FinalAuditTargets.txt`: fully-qualified declarations to probe.
- `FinalAuditImports.txt`: modules the generated probe imports.
- `run_final_axiom_audit.ps1`: generates `FinalAxiomProbe.generated.lean`,
  runs Lean, and checks:
  - Lean EXIT 0;
  - each `#print axioms` list is a subset of
    `{propext, Classical.choice, Quot.sound}`;
  - no `sorryAx` in the axiom output;
  - no source occurrence of `sorry`/`admit` in the audited target files list.
- `FinalAuditFiles.txt`: target source files checked for forbidden markers.

## Manual preconditions

1. Central watchdog reports EXIT 0 for all queued actual files.
2. No target file contains `sorry`, `admit`, project-defined `axiom`, or
   `True`/`PUnit` placeholders used as proof.
3. The comparator or frozen target type is checked against the paper statement.
4. Build artifacts in `.lake/build/lib/lean` are current for the target modules.

## Commands (run after compile green)

```powershell
cd D:\lean
pwsh -NoProfile -File tmp/sheaf/xif/paper/run_final_axiom_audit.ps1
```

Expected output ends with:

```text
AXIOM AUDIT PASS
Axioms: propext Classical.choice Quot.sound
```

Any additional axiom, `sorryAx`, missing declaration, or nonzero Lean exit is a
FAIL and must be reported, not worked around.

## Reporting fields

- Lean EXIT:
- Probe output path:
- Axiom sets per declaration:
- Additional axioms:
- Sorry in audited files:
- Target/frozen type check:
- Audit result: PASS/FAIL

## Norm unification excluded (2026-10-29)

Normalized/default norm equality and coefficient equality are **not** target
conditions.  The exact ratio formula is diagnostic only; see
`QVFamNormalizedNormDiagnostic.md`.
