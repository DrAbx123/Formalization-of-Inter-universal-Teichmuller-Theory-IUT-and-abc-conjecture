# S1245: target SourceOutputPrimeStripInterpretation audit

Read: target file, S1235 report, S1234 integration.
Command: `lake env lean -j1 -R 'D:\lean' -o ... 'LeanFormal/IUT/IUTIII/Theorem311/Output/SourceOutputPrimeStripInterpretation.lean'`.

## Compile

```text
EXIT=0
lines=216
SHA256=42C324AC6007CA219592CAA82CBD111AE8A150491859B6FF6E8AAEE793DF1BB4
```

Same SHA/lines as the S1235 report.  Scan for `sorry|axiom|admit|True|PUnit`:
no matches.

## Axioms (axon trio only)

`#print axioms` on the key actual declarations:

```text
forgetRun_eq_runAlgorithm_target : [propext, Classical.choice, Quot.sound]
finiteKernelRun_forget          : [propext, Classical.choice, Quot.sound]
actualUpperEnv_stripIso         : [propext, Classical.choice, Quot.sound]
sourceRouteTrace_endpoint       : [propext, Classical.choice, Quot.sound]
```

No undeclared axiom, no `sorryAx`.

## Actual fields

- `SourceRun` + `sourceRun`: input, actual `runAlgorithm` output, presentation/
  algorithm records with `rfl` equalities.
- `forgetRun` + `forgetRun_eq_runAlgorithm_target`: actual reduced output.
- `sourceRouteTrace` + `sourceRouteTrace_endpoint`: actual S1170 route trace,
  endpoint = runAlgorithm target.
- `actualUpperEnv` + `actualUpperEnv_stripIso`: actual S1195 non-refl
  upperEnv, stripIso = actual `I.fLinkAt 1 0 1 1`.
- `stripOfChoice`, `stripOfChoice_apply`, `stripOfChoice_exists`,
  `SourceFamilyChoice`: actual source-index to F-prime-strip map.
- `finiteKernelRun`, `finiteKernelRun_forget`: actual finite-kernel SourceRun
  instance from actual W.1/W.4 data and `AlgorithmInput.empty`.

## Exact/conditional fields

- `S1212AdjacentKummerSquareData`: structure with one field
  `square : SourceKummerEvaluationSquare ...`; no inhabitant asserted.
- `S1212UpperEnvNontrivial`: a `Prop` (exists moved element); not proved.

These are the only exact items recorded in the target; neither is replaced by a
`True`/weak wrapper.

## Consistency with S1235

- Target SHA and line count match S1235 exactly.
- Existing actual content preserved: SourceRun/forgetRun/routeTrace/
  actualUpperEnv/stripOfChoice.
- S1234 finiteKernelRun integration present and compiles as part of target.
- S1234 file itself still compiles EXIT=0 against target.

## Verdict

Target compiles EXIT=0, axioms are exactly the allowed trio, no sorry/axiom,
actual/exact split as listed; consistent with S1235.
