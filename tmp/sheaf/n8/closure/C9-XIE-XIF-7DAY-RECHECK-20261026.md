# Xi-e to xi-f: seven-day recheck

Date: 2026-10-26. Purpose: answer the active `XiEToXiFOutputReadoutProjection(C)` task by reusing the 10-24--10-26 source audits and failed-route records, not restarting them. Owner: root, single agent. No Lean or source edits.

## Target and source

Fix one admissible Theorem 3.11 datum `C`, its native q-pilot, actual final-evaluation outputs `P_C`, signed normalized readout `nu_C`, q-readout `Q_C`, and hull bound `h_C`. Useful source-certificate formulations are:

```text
exact:  exists D in P_C, nu_C(D) = Q_C
signed: for every eps > 0, exists D_eps in P_C,
          Q_C - eps <= nu_C(D_eps)
```

Both imply the scalar estimate once `nu_C(D) <= h_C` for every actual output. They are sufficient witness forms; exact attainment is stronger than the paper's scalar conclusion. The source copy `sources/IUT-III.txt` has SHA256 `822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D`.

Corollary 3.12 assumes only that we are in the situation of Theorem 3.11. In xi-e, the fixed-q relation is prescribed by the 1-column arithmetic-holomorphic structure; SHE says relevant operations remain valid/executable under that fixed-q condition; the possible output readouts are linked to the q-pilot through prime-strip isomorphisms. In xi-f, the paper then says the output construction constitutes a construction of the q-pilot readout, perhaps up to indeterminacies/approximation, and says the inclusion follows formally. Thus xi-e/xi-f are internal proof claims, not separately listed external hypotheses. The claim that fixed-q operations are executable is weaker than the q-readout projection.

Important target-strength correction from the 10-25 `C9-XIF-R-DEFINITION-AUDIT`: xi-d explicitly defines `R_{<=h}` as `{lambda in R | lambda <= h}`, a half-line, not as the image of actual outputs `R_possible := {nu_C(D) | D in P_C}`. Therefore `Q in R_{<=h}` is just `Q <= h`; it does not itself provide exact output attainment. Do not silently replace the paper half-line by `R_possible`. Exact/signed output witnesses are valid stronger certificates, but before freezing a Lean target one must choose whether the target is the paper scalar projection or this stronger witness theorem.

## Seven-day findings reused

- 10-24 marked-image and local-global descent records: local structure maps/collections do not automatically give the same global q-to-hull arrow. Their arithmetic model rejects that weak inference only; it is not a full IUT counterexample.
- 10-25 `C9-XIF-ATTEMPTS` and the local/Ind/determinant/IPL/loop/APT audits: local theta-value equality is not hull log-volume; IPL of prime-strips does not preserve the output-region readout; determinant equality would wrongly force hull value equal to q; Ind1/2 preserve readout and Ind3 is one-sided; “fixed point” language supplies no map. The closure/compactness option changes the target unless its topology and signed error are proved.
- 10-25 xi-f reviews: the approximation phrase has no explicit epsilon, sign, or actual output witness. Earlier “closed loop gives exact membership” claims were rejected as unexpanded.
- LANA report, as captured in `C9-C1-LITERATURE-20261025.md`, isolates the same native-q/anabelian-output compatibility as `eta_q = eta^anab_S` and says it has not reconstructed a proof. This is evidence of an unresolved source bridge, not a counterexample.
- 10-26 carrier/sheaf records: the paper IQ/O carrier, hull, `det^M`, reference and readout comparison can be handled conditionally. What is absent is the fixed q-mark's actual attachment to the restricted sQ3/final-evaluation family, or a same-`C` signed output / `S >= kappa` certificate. A1/A2/A3 are independent and need not be Lean-proved first.
- `C9XiESourceConditionLogic.lean` is only a pure logical boundary check: coverage plus the hull upper bound gives `Q <= h`; fixed-q executability/nonempty output alone does not imply coverage.

## What can be proved without circularity

If a source construction independently supplies an exact output witness, its readout is `Q_C`, and hull monotonicity gives `nu_C(D) <= h_C`; hence `Q_C <= h_C`.

For signed witnesses, suppose `Q_C > h_C` and set `eps=(Q_C-h_C)/2>0`. A source-produced `D_eps` satisfies `Q_C-eps <= nu_C(D_eps) <= h_C`, while `Q_C-eps=(Q_C+h_C)/2>h_C`, contradiction. This is a complete scalar proof, but constructing `D_eps` is the unresolved source obligation.

The sheaf construction that would supply the witness must use the actual fixed-`C` q-mark transported by the Remark 3.10.2 `U2 K2` composite, attach it to an actual sQ3 hull-determinant/final-evaluation object, verify local maps and localization/cocycle compatibility, prove descent remains in the permitted output family, and preserve the original `M`, `O(-)` reference, weights and signed readout. cQ3 defines compatible collections; cQ4 transports an existing arrow. Neither creates this designated arrow. The paper's closed-loop assertion says the strip retains both intertwinings, but the reviewed records do not expand that into the required output-readout witness or quantified signed error.

## Verdict and next action

No non-circular proof of the independent `XiEToXiFOutputReadoutProjection(C)` was found in the existing seven-day corpus or constructed in this recheck. The paper asserts the bridge within its Corollary 3.12 proof; accepting xi-e/xi-f as an already-proved source theorem closes the scalar result, but citing xi-f does not independently prove the bridge. There is no source-valid counterexample or disproof.

Next executable mathematical step: for one fixed admissible `C`, inspect the actual evaluation/sQ3 constructor and attempt the marked attachment described above; stop at the first missing constructor. If no such output-map constructor is available, attempt only a same-`C` source-backed signed lower witness or normalized `S >= kappa`. Do not restart A1/A2/A3, abstract sheaf theory, local numerical retuning, reduced C7, or `OriginalInput -> Input`.

Status: `statement_compiles=not_run`, `proof_body_checked=not_run`, `kernel_closed=not_run`, `target_accepted=false`; no Lean, project build, comparator, or independent review was run.
