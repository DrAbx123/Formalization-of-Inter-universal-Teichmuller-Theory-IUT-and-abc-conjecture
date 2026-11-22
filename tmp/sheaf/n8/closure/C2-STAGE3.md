# N8 C2 stage 3 - actual finite-place SourceLogKummerData (PARTIAL; not C2 closure)

> Audit correction (2026-10-23): this file closes only the current `SourceLogKummerData` finite-place fields. It does **not** prove the full N8 C2 paper object. G_v action/action descent, Kummer/root-change, K1/K2 boundary, archimedean branch and multi-place assembly are exact no-go at the present interfaces. See `C2-COMPLETENESS-AUDIT.md`, `C2-ACTION-STAGE1.md`, `C2-KUMMER-STAGE1.md`, `C2-K1K2-STAGE1.md`, `C2-ARCH-STAGE1.md`.

- Task: S3-C2, construct actual SourceLogKummerData I C1.
- Owner: logdescent.
- Lean file: tmp/sheaf/n8/closure/C2Actual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.
- Production edits: none.

## Actual construction

C2Actual.sourceLogKummerDataActual (I C1) has fields:

- localShell p place := sourceLocalLogShellDatum (K := I.initial.arithmetic.Fmod) (p := p) place;
- localShell_eq := rfl;
- kernel_eq_torsion := unitLogHom_ker_eq_torsion;
- logShell_eq := sourceLocalLogShellDatum_logShell_eq_integralLogShell;
- preLogShell_eq := sourceLocalLogShellDatum_preLogShell_eq_range_unitLogHom.

Thus the actual local logarithm is unitLogHom, the kernel is exactly the
torsion subgroup of the integral units, and the log-shell/pre-log-shell are
the production donor's actual integral log-shell and unit-log range.

sourceLogKummerData_nonempty_actual : Nonempty (SourceLogKummerData I C1)
is proved by the actual constructor, with no sorry.

## Exact no-go for the rest of the C2 paper content

The current SourceLogKummerData structure deliberately has no fields for:

1. G_v-invariant submonoid / action descent;
2. actual Kummer/root-change map;
3. K1/K2 boundary comparison;
4. archimedean branch;
5. multi-place assembly over C1's placeEquiv.

These are not assumed as hypotheses and are not added as new fields.  Their
exact missing types are not present in the current C2 interface: there is no
production Lean type for the G_v action/Kummer arrow/K1-K2 boundary in the
C1-indexed multi-place form.  This is an exact no-go for claiming the full
C2 paper object, not a proof gap in the finite-place donor data above.

## Consumer

C4/C5 consume SourceLogKummerData for the finite-place log data; C9/C10 consume
the downstream q/theta construction.  This stage closes only the actual
finite-place data package and its nonempty obligation.

## Status

- statement_compiles: true (EXIT=0).
- proof_body_checked: true for the constructed fields and nonempty theorem;
  no sorry in C2Actual.lean.
- kernel_closed: not run (no axiom audit in this goal round).
- target_accepted: NO for C2; only the finite-place SourceLogKummerData subset is constructed. C2 status = partial; the fancier paper parts remain exact no-go and are not claimed.
