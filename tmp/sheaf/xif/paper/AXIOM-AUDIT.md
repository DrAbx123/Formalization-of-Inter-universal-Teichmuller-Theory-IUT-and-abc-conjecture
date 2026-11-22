# Paper-level xi-f axiom audit

Date: 2026-10-28. Probe file: `tmp/sheaf/xif/paper/XiFAxiomProbe.lean`.
Compiled with `lake env lean -j1 -R D:\lean ...`; EXIT 0.

## #print axioms output

```text
Proof.paperXiF_of_thetaLink: [propext, Classical.choice, Quot.sound]
CompileGate.paperXiF_assembly_conditional: [propext, Classical.choice, Quot.sound]
paperXiF_conditional_status: [propext, Classical.choice, Quot.sound]
paperXiF_final_bound: [propext, Classical.choice, Quot.sound]
Proof.paperXiFResult_of_obligations: [propext, Classical.choice, Quot.sound]
```

Only the three allowed Lean/Mathlib axioms are used. No project axiom, no sorry.

## Notes

- `paperXiF_assembly_conditional` is conditional on the explicit Theta-link identification; it does not assert an inhabitant.
- Exact source obligations remain: q-pilot paper identifications, IQ-carrier realization/compactness, link_identification, link_implies_inclusion, O-module/SHE/IPL/APT source instances.
- No value-layer surrogate is imported by the paper-level gate.
## Closed actual q-pilot scalar identification

- `LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.signedQPilotLogVolume_eq_paperQPilotLogVolume`
  depends only on [propext, Classical.choice, Quot.sound].
- `signedQPilotLogVolume_eq_neg_abs_qParameter` depends only on the same three axioms.
- File: tmp/sheaf/xif/paper/QPilotScalarIdentificationActual.lean (EXIT 0).

## Canonical q-pilot identification construction

- `LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual.qPilotIdentificationActualOfCanonical`
  depends only on [propext, Classical.choice, Quot.sound].
- Files: QPilotCanonicalConstruction.lean, QPilotIdentificationConstruction.lean (both EXIT 0).

## Actual one-column / q-pilot construction

- sourceOneColumnActual and paperQPilotObjectActualOfNumberField depend only on [propext, Classical.choice, Quot.sound].
- File: OneColumnActual.lean (EXIT 0).

## IQ carrier from C7 obligations

- image_subset_c6Hull_of_obligations and paperIQCarrierActualOfObligations depend only on [propext, Classical.choice, Quot.sound].
- File: IQCarrierObligationsActual.lean (EXIT 0).
- This closes the theta-image containment donor at the actual C6 hull; literal IQ O-module/compactness/unit-region/log-volume fields remain explicit obligations.

## IQ and SHE closures

- IQCarrierObligationsActual.lean EXIT0: image_subset_c6Hull_of_obligations + paperIQCarrierActualOfObligations depend only on [propext, Classical.choice, Quot.sound].
- SHEMissingActual.lean EXIT0: paperSHEMissing_actual depends only on [propext, Classical.choice, Quot.sound].

## Actual IndActionData

- paperIndActionsMissing_actual depends only on [propext, Classical.choice, Quot.sound].
- File: IndActionsActual.lean (EXIT 0); inhabits PaperIndActionsMissing at the actual C4 carrier using C4.ind.
