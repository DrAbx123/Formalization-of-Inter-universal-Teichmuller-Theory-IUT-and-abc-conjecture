# C1 marked hull gate: fixed-C recheck

Date: 2026-10-26. Owner: root, single agent. SHEAF stage 1. This is a narrow
addendum to the existing C1 record; it does not repeat the earlier carrier,
LANA, numerical, or A1/A2/A3 investigations.

## Task package

- Target: `n8-c9-final-evaluation-capsule`, with consumer Corollary 3.12's
  same-C scalar comparison `Q_C <= h_C`.
- Scope: determine whether the actual source statements about the final
  evaluation, IPL, SHE, and sQ3/cQ3 construct the q-marked arrow into the
  paper IQ/O hull without using xi-e/xi-f as premises.
- Quantifiers: fix one arbitrary paper-admissible complete datum `C`, its
  native q-pilot, Theta/LGP gluing, procession, output family, determinant
  power `M`, inverse `O(-)` reference, weights, and signed normalization. No
  change of `C` or normalization is allowed.
- Read-only sources: `tmp/sheaf/n8/closure/sources/IUT-III.txt`;
  `SourceTheorem311Assembly.lean`; `SourceFaithfulBoundary.lean`;
  `SourceMultiradialIplLinkWiring.lean`; `SourceSHETransportLaws.lean`;
  `C9-CARRIER-ONE-SIDED-REUSE-20261026.md`; prior LANA and marked-image notes.
- Written files: this note, the existing final-evaluation DAG node, `STATE`,
  `queue`, and `AUDIT_LEDGER`. No Lean definition or shared mathematical
  definition changed. No other active owner was contacted.

## Natural-language route that runs

Fix the data above. Let `P_C` be the actual final-evaluation output family,
`H_C` its paper holomorphic hull in the IQ/O carrier, and `nu_C` the readout
after the same `det^M`, `O(-)` reference, weights, and signed normalization.
Let `Q_C` be the readout of the fixed q-pilot and `h_C = nu_C(H_C)`.

1. Every actual output region `D` lies in its least `lambda O` hull. Applying
   the same determinant and reference gives `nu_C(D) <= h_C`. If a different
   reference lattice occurs, retain its actual relative-index correction; it
   cannot be chosen after inspecting `Q_C-h_C`.
2. The explicit Remark 3.10.2 composite used by IPL transports the existing
   q-pilot prime-strip/pilot isomorphism class. The intermediate composition
   reduces to `U2 K2`. The finite-etale arithmetic hull/Haar transport already
   recorded in `C9-CARRIER-ONE-SIDED-REUSE-20261026.md` supplies the carrier
   and readout comparison when its actual source map is given.
3. At sQ3, an actual output inclusion into `H_C` induces the output-side
   structure poly-morphism to the normalized hull determinant. If the
   transported q-mark is an object in this same restricted category, with
   compatible localization maps and cocycle, and the comparison retains the
   original degree normalization, the Frobenioid order/readout gives the
   required one-sided comparison. Alternatively, an actual family
   `D_eps in P_C` with `Q_C-eps <= nu_C(D_eps)` and `nu_C(D_eps) <= h_C`
   suffices. If `Q_C > h_C`, choose `eps=(Q_C-h_C)/2`; the inequalities
   contradict one another.

This is a valid sheaf/order proof **conditional on the marked source landing**.
It avoids an exact representative if a signed-epsilon family is available.

## Attempt to construct the marked landing

The needed datum is not merely an isomorphism of prime-strips. For the fixed
`C`, one needs an actual q-to-hull structure morphism (or a source output
family) whose local maps satisfy the localization square, whose overlaps
satisfy the cocycle, and whose global object stays in the original
final-evaluation/further-rigidification family with unchanged `M`, reference,
weights, and signed readout.

The source checks do not construct this datum:

- Remark 3.11.1(iii) supplies IPL and the explicit strip-isomorphism composite;
  it also says the final evaluation has various further rigidifications.
  It does not identify the fixed q-pilot mark as a member of that restricted
  output fiber.
- SHE says the operations remain executable under the fixed q-pilot
  condition. This is a condition on the operations; it is not a surjectivity
  or essential-image theorem for their output family.
- cQ3 defines the hull-side category using objects already equipped with a
  structure poly-morphism to the hull determinant. The statement that such
  collections exist does not produce the specific q-marked object or its
  map. cQ4 transports an existing arrow and corrects allowed vertical shifts;
  it cannot create that arrow.
- Remark 2.4.2(v)-(vi) permits different further rigidifications over the
  same underlying global realified Frobenioid data. Thus transporting the
  unmarked strip or gluing local squares does not by itself fix the q-scale.
  The source arithmetic input needed to pin that scale (including the
  FrdII 5.6.3 comparison) remains to be supplied.
- The earlier `C9-C1-FULL-TH310-BASIS-20261025.md` sentence that the q-pilot
  is “one of the possible rigidifications” is an inference, not a consequence
  of the cited phrase “various possibilities.” Preserve the historical note;
  do not use that sentence as a proved edge.

The paper then states the missing projection in xi-e/xi-f: it concludes that
the constructed output readouts, perhaps approximately, include the fixed
`Q_C`. Accepting xi-e/xi-f as a source theorem makes the scalar argument
formal, but that is the disputed compatibility assertion itself. Remark
3.9.5(ix)'s closed-loop statement is also source text, not a construction of
the missing marked arrow from cQ3/cQ4 alone.

## Lean boundary and exact status

The current Lean layer confirms why a proof cannot be assembled from the
existing cards. `Theorem311Output` in `SourceFaithfulBoundary.lean` records
Part I/II/III, profile quotient laws, and evaluation squares, but no q-pilot
mark, IQ/O region, or final-evaluation rigidification family.
`ReducedIplLink` in `SourceMultiradialIplLinkWiring.lean` is a route relation on
`Choice`; its header explicitly omits the output prime-strip object and
source-level IPL. `SourceSHETransportLaws.lean` is a reduced localization
interface, not the operation-level fixed-q readout. `C9IUTBridgeOutput.lean`
therefore keeps q-pilot membership as a separate explicit obligation. These
are interface facts, not a counterexample to the full source theorem.

Result: paper IQ/O carrier typing, determinant/reference comparison, and the
conditional scalar proof run. The independent source gate does **not** close.
The exact leaf remains `FinalEvaluationQMark`: construct membership in the
actual restricted output family, a signed-epsilon lower witness, or an actual
same-C normalized `h_C-Q_C=S_C-kappa_C` ledger with `S_C >= kappa_C`.
The existing `b=3, B=I` gain is not an instance because the actual branch and
global/reference contribution remain unconstructed. No source counterexample
or theorem refutation has been found.

## Verification and next action

- `statement_compiles`: not applicable; this package adds no Lean statement.
- `proof_body_checked`: not run.
- `kernel_closed`: not run.
- `target_accepted`: false; independent source landing remains open.
- No Lean, Project build, comparator, or independent review was run.

Next action: for one fixed admissible `C`, trace its splitting generator and
`rho_v` through `U2 K2` into the actual final-evaluation/sQ3 rigidification
object. Produce the local maps, localization square, cocycle, restricted
family membership, and readout with the frozen normalization; if this object
does not exist in the current source construction, stop at that named
constructor and switch only to a same-C `S>=kappa`/signed-epsilon certificate.
A1/A2/A3 are not prerequisites, and the waived `OriginalInput -> Input`
construction stays waived.
