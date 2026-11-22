# C1 hull-carrier compatibility: single-agent natural-language proof audit

Date: 2026-10-26. Owner: root, single agent. SHEAF stage 1. No Lean edit.

This record gives the proof as far as the source objects justify it, identifies
the first unproved inference, and reuses the 10-16--10-25 carrier, LANA,
marked-image, local-global, and numerical investigations. It corrects the
unqualified “paper-level gate closed” wording in
`C9-MARKED-CLOSED-LOOP-NATURAL-20261026.md`: that scalar conclusion is closed
only when xi-e/xi-f are accepted as the source assertion being formalized.

## Fixed target

Fix one complete paper-admissible datum `C`, including its native q-pilot,
Theta/LGP gluing, procession, original weights, determinant power `M`, `O(-)`
reference, and signed normalization. Let `P_C` be the actual final-evaluation
output family, `H_C` its paper holomorphic hull, and `Q_C`, `h_C` the signed
normalized readouts of the q-pilot and hull. The target is `Q_C <= h_C` for this
same `C`.

An exact output is stronger than needed. A valid source alternative is a family
`D_eps in P_C` with `Q_C - eps <= nu_C(D_eps)` for every `eps > 0`, using the
same `M`, reference, weights, and normalization.

## Proof chain that does run

1. **Paper carrier.** Theorem 3.11 supplies IQ/log-shell tensor packets with
   mono-analytic integral structure. Remark 3.9.5(i) forms the least `lambda O`
   hull of each actual output region (or the whole packet in the
   non-relatively-compact case). The current Lean value-monoid hull is not this
   carrier; its `top`-volume diagnostic is not a paper counterexample.

2. **Common comparison object.** `O`-stability makes a finite hull an
   arithmetic vector bundle. Ob3 takes the weight-compatible `det^M` and
   tensors by the inverse `O(-)` determinant. cQ3 places the resulting objects,
   their local Galois/unit actions, structure poly-morphisms, and localizations
   in the q-codomain local/global Frobenioids. A genuine finite etale
   `Q_p`-algebra isomorphism transports integral closure and fractional-ideal
   hulls; unit-relative Haar scaling cancels. A changed reference lattice
   contributes the exact relative-index correction `delta`, which cannot be
   selected after seeing the gap.

3. **Marked transport before volume.** The commuting squares of Remark 3.10.2
   reduce the IPL composite to `U2 K2`. By II.4.9(viii), the splitting
   generators and `rho_v` defining the q-pilot are natural under the full
   prime-strip isomorphisms, so the existing pilot isomorphism class is
   transported. cQ4 preserves the local Galois/unit data through the
   log-Kummer vertical adjustment, modulo the allowed log-link iterates.
   Remark 3.9.5(ix) asserts that the chain through sQ3/sQ4 is closed up to the
   stated formal quotient indeterminacies, before sQ5 forgets the arithmetic
   structure.

4. **Hull bound.** With the same `M`, `O(-)` reference, weights, and signed
   convention, hull minimality and Haar monotonicity give

   ```text
   nu_C(D) <= h_C   for every actual D in P_C.
   ```

These steps solve the paper-carrier typing and transport problem. They do not
by themselves prove the scalar target.

## Exact remaining inference

To infer `Q_C <= h_C`, one still needs one of

```text
exact:  exists D in P_C, nu_C(D) = Q_C;
signed: for every eps > 0, exists D_eps in P_C,
        Q_C - eps <= nu_C(D_eps).
```

The scalar proof is then elementary. If `Q_C > h_C`, take
`eps = (Q_C-h_C)/2`; the witness gives
`Q_C-eps <= nu_C(D_eps) <= h_C < Q_C-eps`, a contradiction. This does not
define an output by its desired value: `D_eps` must come from the actual
final-evaluation algorithm.

The first unproved source inference is therefore the attachment of the
transported q mark to the restricted further-rigidification/output family at
sQ3. IPL transports an existing marked prime-strip; it does not alone prove
that the fixed mark lies in that restricted family. cQ3 describes compatible
local/global collections and structure poly-morphisms; collection existence is
not a q-to-hull arrow. cQ4 corrects vertical shifts but cannot create an absent
marked arrow. A strict global morphism is one sufficient route, with

```text
loc_v(g) o lambda_q,v = lambda_H,v o u_v,
```

using the original degree and reference data. It is not necessary if a real
source lower bound or signed epsilon family is constructed.

For the local arithmetic ledger, the exact audited form is

```text
h_C - Q_C = S_C - kappa_C.
```

`S_C` is the actual source-allowed gain and `kappa_C` the reference/divisor
defect. Proving `S_C >= kappa_C` closes the scalar target; `kappa_C = 0` is
stronger than necessary. The earlier Q/3 construction shows that local
compatible maps and a cQ3-shaped collection can coexist with a global defect;
it is a diagnostic against that inference, not an IUT counterexample.

## Other routes checked

- **Closed loop / category:** Remark 3.9.5(ix) and Remark 3.12.2(fitw) explain
  the paper's `q-itw => q-itw AND Theta-itw/indets => Theta-itw/indets`
  projection. They do not, without xi-e/xi-f, give a quantified element of
  `P_C` with readout `Q_C`.
- **Sheaf descent:** descent glues already-constructed local marked maps when
  their localization squares and cocycle are supplied. It cannot create those
  maps or certify membership in the restricted output family.
- **Order, convexity, compactness:** `nu(D)<=h_C` for all outputs says nothing
  about a separate `Q_C` without membership, a lower witness, or a
  source-justified closure statement. APT/SHE names do not supply these.
- **LANA eta route:** the required pre-volume comparison is
  `eta^q = eta^anab_S`. Existing inverse-scaling and scalarized ETA probes are
  audited as tautological or wrong-carrier controls; admissibility of the
  q-pilot integral structure remains a named source condition. This is the
  same compatibility question one layer earlier, not a bypass.
- **Numerics:** the exact `J_H` computation retains the `j^2` procession
  factor; at `ell=41` the seed is short by `285L/164`. The `b=3, B=I` surplus
  and the `rho=1/2, b=1347` success are conditional/local profiles, without
  the original complete-C source attachment. They do not supply the witness.

## Direction and status

A1/A2/A3 should not be placed first: they are independent at the accepted
`Theorem311Source.Input` boundary and do not provide the q-mark witness. Keep
that Lean proof and the waived `OriginalInput -> Input` construction unchanged.

The next mathematical package is one fixed admissible `C`: follow the fixed
splitting generator and `rho_v` through `U2 K2` into the actual sQ3
evaluation/further-rigidification object, recording its image, local maps,
cocycle, `M`, reference, weights, and signed degree. Decide whether it gives
exact membership, a quantified signed approximation, or `S_C >= kappa_C`. If
the first mark-to-output constructor is absent, preserve that named source gap
instead of tuning numerical parameters or restarting a general carrier survey.

Current result: paper-carrier/determinant compatibility and the conditional
scalar proof are explicit; an independent proof of C1 is not obtained.
`n8-c9-final-evaluation-capsule` remains stage1 open,
`proof_status=open`, `target_accepted=false`. No Lean, Project build,
comparator, or independent review was run in this package.
