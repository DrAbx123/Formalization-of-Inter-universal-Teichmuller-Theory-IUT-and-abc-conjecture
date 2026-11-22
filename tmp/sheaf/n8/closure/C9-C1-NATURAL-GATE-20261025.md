# C1 hull-carrier compatibility gate: natural-language proof attempt

Date: 2026-10-25. SHEAF stage 1. Owner: root. Status: open; target_accepted=false.

This record consolidates the 2026-10-16--25 evidence for the current C1 gate. It
does not reopen `OriginalInput -> Theorem311Source.Input`, which the user accepted
as the boundary for the A1/A2/A3 proof. It also does not treat a conditional
profile calculation, a test carrier, or a Lean contract field as a source proof.

## 1. Target to prove

For one fixed admissible initial Theta-data set, fixed selected places, procession
weights, gluing, and the paper normalization, let `R` be the readouts of the
actual final-evaluation output family and let `Q` be the signed q-pilot readout.
The scalar conclusion needed by Corollary 3.12 is

```text
  every r in R satisfies r <= h,    and    Q belongs to R,
  hence Q <= h.
```

The stronger statement

```text
  exists D in the possible-output family, logVol(D) = Q
```

is an exact-attainment version. It may be useful, but it is not required if the
source proves an explicit signed epsilon approximation sufficient for `Q <= h`.
The phrase in xi-f that the construction may work only “up to some sort of
approximation” must therefore be represented by a quantified error statement,
not silently replaced by exact attainment.

## 2. Natural-language proof that would be valid

Fix a place `v_Q`, procession index `n`, and label `j`.

1. Construct the actual common carrier `E`: the arithmetic/log-shell tensor
   carrier used by the final evaluation and by the q-pilot representation. Its
   integral region `O_E`, Haar measure, determinant/power operation, and reference
   normalization must all be the same objects on both sides.

2. Construct the finite canonical hull `H_E = lambda * O_E` containing every
   final-evaluation output region. Holomorphic-hull minimality and Haar
   monotonicity then give `nu(U_out) <= nu(H_E) = h` for every output readout.

3. Construct the q-pilot region `U_q` in this same carrier and compute its readout
   from the q-pilot line/determinant normalization. Proposition 3.9 and the
   fixed q-pilot data must give `nu(U_q) = Q`, with the signed convention
   `Q = -|log q|` and `h = -|log Theta|`.

4. Prove the source-level final-evaluation/rigidification arrow: the q-pilot
   rigidification is an allowed member of the actual output family, or is the
   limit of a source-allowed family with an explicit signed error. This is the
   essential-image statement behind xi-e/xi-f; it is not supplied by the words
   “APT”, “SHE”, or “full poly-isomorphism” alone.

5. Apply the scalar order argument. In the exact case, `Q = nu(U_q)` is one of
   the `r` in `R`, so `Q <= h`. In the approximation case, if for every
   `epsilon > 0` a genuine output has `Q - epsilon <= r <= h`, then assuming
   `Q > h` and taking `epsilon = (Q-h)/2` is a contradiction. This proof uses no
   exact representative, but it does require real source output witnesses and a
   signed error bound.

This is the non-circular proof shape. It does not infer an output from the scalar
decomposition of `Q`, and it does not identify a hull with an output object.

## 3. What the repository actually proves

### Arithmetic side already available

The finite-place tensor/IQ files construct real finite local packets, integral
log-shell regions, canonical `lambda * O` hulls, positive finite Haar measures,
and decomposition-independent normalized local readouts. The 2026-10-16 and
2026-10-17 records (`finite-place-iq-hull-interface.md`,
`iq-hull-haar-logshell-landing.md`, `source-polyisomorphism-gap-20261017.md`)
also record the exact tensor, lattice, and finite-index results that can be
reused once a source output is landed in this carrier.

### Source value hull diagnostic

`SourceImageHull.lean` defines `sourceHolomorphicHull` as the least submonoid
closed under every componentwise non-unit scaling. `SourceImageHullVolume.lean`
defines its volume as the supremum of source log-degrees. Under the explicit
pointwise degree-faithfulness hypothesis

```text
  logDegreeAt (posRealAction (ofAdd b)) = b   for every real b,
```

constant positive scalings of arbitrarily large degree are legal hull scalings.
Scaling one hull point therefore produces unbounded log-degree, and
`C1FiniteHullObstruction.lean` proves `sourceHullVolume = top`. The result is
kernel-closed with only the standard three Lean axioms. It is an obstruction to
the current value carrier as a finite paper hull, not a counterexample to IUT.

`SourceArithmeticThetaPilotBridge.lean` strengthens the diagnosis: a bounded
arithmetic canonical hull cannot cover this entire faithful source hull while
preserving degree. Therefore the next carrier must be a paper-faithful
restricted/actual IQ-O-module carrier, or the source hull definition must be
reworked with a source-justified bounded scaling family. An arbitrary map from
the full value hull to a finite arithmetic hull is ruled out.

### Lean bridge and signed-readout diagnostic

`C9IUTBridgeOutput.lean`'s `C1SourceBridge` is only a membership field for an
abstract possible-output set. It does not identify the output as the actual
q-pilot, and it has no `logVol(output) = Q` field. The singleton probe
`C9C1IdentifiabilityProbe.lean` proves that this membership can hold while exact
attainment fails. This is an interface-level non-implication, not a
source-valid IUT countermodel.

`C9IUTBridgeContract.lean` compares a negative `qPilotLog` with
`ENNReal.toReal hullVolume`. Since the latter is nonnegative, the displayed
inequality is automatic once the bridge exists. It is not the paper's signed
comparison `Q <= h`. `CertificateHullWiringSigned.lean` records the same issue.

## 4. Why the recent numerical routes do not close C1

The 2026-10-24/25 evaluation-defect, marked-height, symplectic-span, and
`p=12301` calculations are useful local diagnostics. They produce exact local
indices, conditional branch thresholds, and in some cases a genuine nonzero
source-generated quantity. They do not, by themselves, supply the four objects
in steps 1--4 above:

* no complete source `C` with all global places, weights, archimedean region and
  target conditions is constructed;
* the local outputs are not shown to be the final-evaluation family in the same
  global carrier;
* the `B=I`/`B=O_K` branches and the required H_A integrality data remain
  underdetermined in the source records;
* the corrected sign audit says a finite lower bound on `h_C` gives an upper
  bound on `F = Q_C - h_C`; it does not give the upper bound needed for a
  counterexample;
* canonical versus normalized `Q` still has a factor/normalization obligation.

Consequently the numerical gap is downstream of C1. It can decide a fixed
profile after a source capsule exists, but it cannot manufacture the missing
q-pilot landing or common normalization.

## 5. First unproved source constructor

The first missing arrow is now precise:

```text
actual final evaluation + q-pilot rigidification
  -> (U_out, U_q) in one paper-faithful E
  -> determinant/power/readout nu with nu(U_q) = Q.
```

The repository has reduced/localization records and arithmetic-side donors, but
no constructor that carries the actual final-evaluation object, its integral
region, and its pilot tag into the same `E` while preserving the paper's signed
procession normalization. This is earlier than exact attainment, and earlier
than any need to finish the A1/A2/A3 wrapper.

## 6. Decision and next action

* Keep `C9A1A2A3Source.lean` as a closed proof on the accepted `Input` boundary.
  Do not extend it as a C1 prerequisite.
* Do not use the current faithful value hull for a finite `h` bridge.
* Create a `FinalEvaluationCapsule` statement with actual output family,
  common-carrier maps, determinant/power compatibility, signed readout equality,
  and either exact membership or a signed epsilon witness.
* Stop at the first missing source constructor if no such capsule can be built;
  do not fill it with an arbitrary `Function`, a singleton possible-image, a
  volume-matched measurable set, or a conditional numerical profile.

Status: arithmetic donors and the conditional scalar proof are available;
source landing, signed normalization, and q-pilot membership/approximation are
open. No Lean or full-project acceptance is claimed for this gate.
