# `FinalEvaluationQMark` dependency audit

Date: 2026-10-26. Owner: root, single-agent review. SHEAF stage 1.

## Scope

This note checks the last 48 hours of C1 work and the existing Lean records. It
does not reopen A1/A2/A3, the waived `OriginalInput -> Input` construction, the
old numerical tracks, or the abstract sheaf argument. The question is whether
an existing construction already proves `FinalEvaluationQMark`, and if not,
where the first missing source constructor occurs.

## Minimal logical target

For one fixed paper-admissible datum `C`, the useful exact/signed target is

```text
exact:  exists D in the actual final-evaluation family, nu(D) = Q;
signed: for every eps > 0, exists D_eps in that family,
        Q - eps <= nu(D_eps).
```

The minimal scalar witness is q's readout in the closure of the readouts of
actual permitted output data. Together with the independently established
upper bound for each permitted output, it gives `Q <= h` by the midpoint
argument. An exact output is sufficient but stronger than the paper's
approximation wording. A q-to-hull structure morphism with local squares and
cocycle is one sufficient construction route, not a logically necessary form
of the target; a same-`C` `S >= kappa` certificate is another route.

At paper level, xi-e states that the operations used in the output construction
remain valid under the fixed q-pilot log-volume condition, and xi-f draws the
output-readout projection, allowing approximation for the indeterminacies.
Taking xi-e/xi-f as accepted source theorems closes the paper's scalar
inference. An independent proof must construct or derive this projection; it
cannot cite xi-f as evidence for the same disputed step.

The repository's reduced C7/IQ branch is a separate formalization attempt. It
provides exact reductions and conditional constructors, but no verified edge
from its `tensorUnit`/canonical-hull target to the paper-faithful final
evaluation readout. It must not silently replace the active C1 target.

### Reduced C7 route: q-pilot carrier landing

The existing Lean reductions prove

```text
qPilotPoint = tensorLanding q = tensorUnit
```

and reduce q-pilot hull membership to

```text
tensorUnit in the canonical IQ hull.
```

Evidence: `C7QPilotActualAttempt.lean`,
`C7QPilotMembershipUnderconstrained.lean`,
`C7-c-qPilot-membership-STAGE1.md`.

This is a real reduction, not a proof of membership. The frozen `tensorUnit`
is a unit, but no source integrality theorem currently places it in the bounded
`lambda O`/IQ hull. The over-F/Fmod completion mismatch is also still present.

### Reduced C7 route: actual evaluation to the IQ carrier

`C7U2IQSourceAttempt.lean` gives a conditional constructor:

```text
EvalToCompletionDonor
  + EvalToCompletionHullCondition
  -> ActualSourceUToIQMap.
```

The first record needs a real map from the actual evaluation point carrier to
the completion used by `tensorLanding`; the second needs containment of its
actual image in the canonical hull. `C7EvalCompletionHullAttempt.lean` reduces
the second condition to `ThetaImageContainmentDonor`. Neither donor is
constructed by the current source interfaces.

### Active C1 gap: restricted output-family membership and normalized readout

Even after a carrier landing, C1 needs the transported q mark to be an output
of the actual restricted final evaluation, with the same localizations,
cocycle, determinant power `M`, `O(-)` reference, weights, and signed
normalization.

`C9IUTBridgeOutput.lean` deliberately keeps q-pilot membership as an explicit
`C1SourceBridge` field. `C9C1IdentifiabilityProbe.lean` proves that this
membership can hold while exact `logVol = Q` fails, so that bridge is not a
readout proof. `C7QPaperNormalized.lean` leaves the mass formula and normalized
identification conditional. `P6ReadoutCarrierFromSourceAllowedAttempt.lean`
leaves the global `Adm` reference/region, support, procession weights and
dimensions as a named gap.

## What is proved and what is not

Proved or kernel-checked in the relevant records:

* In the reduced C7 route: q-pilot-to-`tensorUnit` equalities and exact
  membership reductions; conditional construction of an IQ map from an
  explicitly supplied evaluation donor and hull containment.
* In the paper-faithful C1 route: conditional hull/readout upper bounds for
  actual outputs, and the scalar argument once the xi-f output projection is
  supplied.
* The abstract non-implication that a membership bridge alone does not imply
  exact q readout.

Still source assumptions or open constructors:

* In the reduced C7 route: source integrality/bounded-hull membership of
  `tensorUnit`, and the actual evaluation-to-completion map/image containment.
  Their connection to paper-faithful C1 is not verified.
* In the active C1 route: operation-level construction/verification of the
  xi-e fixed-q condition and its xi-f output-readout projection, with the
  permitted-output provenance and normalization; alternatively, a same-`C`
  signed output or `S >= kappa` certificate.

The paper text in Corollary 3.12 (xi-e)--(xi-f) asserts the output-readout
projection. Accepting that assertion as source input closes the paper-level
scalar step. It does not constitute an independent derivation of the three
constructors above, and it is not represented as a closed Lean theorem here.

## Why the 48-hour investigation stalled

Most routes closed a conditional statement or used a reduced/surrogate carrier.
The old value-monoid and C6 routes do not model the paper IQ/O carrier; the C7
`tensorUnit` route has no verified consumer edge to the active C1 readout; the
singleton bridge does not identify q's readout; local-global collection and
full-strip/IPL transport do not perform xi-f's output projection; numerical
profiles do not realize a complete fixed `C`. A1/A2/A3 only control already
existing outputs and cannot supply this connection.

## Revised decision

The active C1 node should name its exact missing leaf as
`XiEToXiFOutputReadoutProjection`. Keep the marked-sheaf arrow and the
`S >= kappa` ledger as alternative sufficient proof routes, not mandatory
definitions of the goal. Keep the reduced C7 route separate until an actual
paper-source consumer edge is verified.

```text
fixed q-pilot condition
  -> actual q-constrained operations (xi-e / SHE)
  -> actual permitted output readout projection (xi-f, exact or approximate)
  -> Q <= h using the already-controlled hull readouts.
```

Next, do not restart the reduced `tensorUnit` membership branch as if it were
the C1 proof. Resolve whether the exact source meaning of xi-e supplies an
operation-level theorem from which xi-f's readout projection follows, or
whether xi-f must be accepted as the paper's source theorem. If deriving it
independently, require a real output readout with provenance; do not add a free
membership/readout field. A1/A2/A3 remain independent and need not be proved
first.

## Acceptance status

No production Lean file was changed by this audit. No new Lean, Project build,
comparator, or independent review was run. The note records existing proof
evidence only; C1 remains `stage1=open`, `proof_status=open`,
`target_accepted=false` under the independent-Lean reading.
