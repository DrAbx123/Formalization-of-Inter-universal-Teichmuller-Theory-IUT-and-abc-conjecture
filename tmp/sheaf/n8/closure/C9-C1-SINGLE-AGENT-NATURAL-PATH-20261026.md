# C1 hull-carrier compatibility: single-agent natural-language path

Date: 2026-10-26. Owner: root, one agent. SHEAF stage 1.

This note records a direct reread of the paper text and the current source
interfaces. It answers the narrow question whether the hull-carrier gate can
be run in natural language, and separates that paper-level route from the
independent Lean source-construction obligation.

## Fixed objects and target

Fix one complete admissible datum `C`, one `Theta x mu LGP` link, its native
q-pilot prime-strip, the procession, the original weights, the determinant
power `M`, the inverse `O(-)` reference, and the signed log-volume
normalization. Let

* `P_C` be the family of possible output data produced by the Theorem 3.11
  multiradial algorithm, including its stated indeterminacies;
* `H_C = phi(P_C)` be the paper holomorphic hull of the union of those
  regions;
* `nu_C` be the signed, procession-normalized readout after `det^M` and the
  `O(-)` correction;
* `Q_C = -|log(q)|` and `h_C = -|log(Theta)|` be the q-pilot and hull
  readouts in that same ordered real line.

The scalar goal is `Q_C <= h_C`. An exact output is stronger than needed. A
source-quantified family `D_eps in P_C` with
`Q_C - eps <= nu_C(D_eps)` for every `eps > 0` is sufficient.

## The paper-faithful route

1. **Start with the correct carrier.** Theorem 3.11(i)(a) supplies the
   mono-analytic tensor packets and their integral structures. Remark 3.9.5(i)
   defines the hull as the smallest region of the form `lambda * O` in the
   IQ/log-shell carrier. This is the carrier used below. The current Lean
   value-monoid hull is a different object; its `top` diagnostic is not a
   counterexample to the paper hull.

2. **Produce the output family with the q constraint still present.** The
   multiradial algorithm is run on the fixed abstract
   `F^(boxplus-triangleright-x-mu)` prime-strip. Remark 3.11.1(iii) gives IPL:
   each intermediate/output prime-strip is connected to the fixed q-pilot
   prime-strip by the algorithmic composite (inverse lower evaluation legs,
   first vertical Kummer leg, then the upper evaluation legs). This is a
   relation between the generated output data and the fixed q input, not an
   arbitrary set-theoretic transport chosen after the fact.

3. **Use SHE/APT as a simultaneous construction property.** Remark 3.11.1(iii)
   and (iv) say that both the construction and its output are valid relative to
   the Theta-side and q-side arithmetic holomorphic structures. APT is an
   algorithm valid for both structures, not a function that simply moves one
   region. The q-side structure is held fixed/coric in the sense of Remark
   3.12.2(ii). Thus the algorithm cannot silently discard the q-intertwining
   while changing the Theta-side ring structure.

4. **Follow the actual quotient chain.** Apply (sQ1) Kummer detachment and
   (sQ2) Galois evaluation, then (sQ3) pass from regions to positive tensor
   powers of hull determinants and apply the `upper-S` quotient, then (sQ4)
   correct the vertical log-Kummer shift. Only after these operations is (sQ5)
   the signed log-volume projection taken. Ob3/Ob4 ensure that the weighted
   `det^M` object, tensored by the inverse `O(-)` reference, is in the same
   local/global Frobenioid comparison frame as the q-pilot. Ob9 says the
   tensor-power, upper-semi, and log-link indeterminacies do not change the
   coarse degree readout once this comparison has been made.

5. **Obtain the carrier bound.** Every `D in P_C` is contained in `H_C` by
   hull minimality. Haar/log-volume monotonicity, with the same `M`, reference,
   weights, and signed convention, gives

   ```text
   nu_C(D) <= nu_C(H_C) = h_C.
   ```

   A changed reference lattice contributes the actual relative-index correction;
   it is fixed by `C` and cannot be selected to repair a numerical gap.

6. **Identify the q readout before taking the scalar projection.** Corollary
   3.12 proof (xi-c) and (xi-d) state that the algorithm plus hull produces
   output data in the 1-column hull which are linked by IPL to the
   representation of the q-pilot, and are expressed using the 1-column
   arithmetic vector bundles. The q-pilot is not redefined as an arbitrary
   element of the hull; its fixed prime-strip/intertwining is the input that
   the simultaneous construction preserves.

7. **Use xi-e and xi-f for the final projection.** Xi-e states that
   expressibility relative to the 1-column structure means the operations are
   executable while the input prime-strip's pilot log-volume is the fixed
   `Q_C`. Xi-f then states that the constructed output log-volume set is,
   possibly up to the paper's stated approximation indeterminacies, a
   construction of that q-pilot log-volume. In the notation above this is

   ```text
   exact reading:   exists D in P_C, nu_C(D) = Q_C;
   weak reading:    forall eps > 0, exists D_eps in P_C,
                    Q_C - eps <= nu_C(D_eps).
   ```

   This is the paper's source assertion that supplies the fixed-q marked
   landing. It is not obtained merely from the existence of a cQ3 collection.

8. **Finish with order, without a hidden identification.** Under the weak
   reading, assume `Q_C > h_C` and choose
   `eps = (Q_C - h_C)/2`. Then

   ```text
   Q_C - eps <= nu_C(D_eps) <= h_C < Q_C - eps,
   ```

   a contradiction. The exact reading is the `eps = 0` special case. This
   proves `Q_C <= h_C` once xi-e/xi-f is accepted as the source-level
   construction claim.

## What this does and does not prove

There are two different statements called C1 in the working tree.

* **Logical position relative to A1/A2/A3.** The accepted Lean A1/A2/A3
  boundary gives output/law/hull data and the upper bound for outputs already
  known to be in the family. It does not give the marked q landing in step 7.
  Therefore C1 is independent of those three proof bodies and they do not need
  to be Lean-proved first. The waived `OriginalInput -> Input` construction is
  also not reopened.
* **Paper source position.** If the full Theorem 3.11 + IPL/SHE/APT source
  theorem and xi-e/xi-f are accepted at their stated strength, step 7 is part
  of the source theorem's conclusion, so C1 is not an additional mathematical
  premise. It is the q-intertwining-preserving output projection of that
  theorem, and the scalar inequality follows formally.

The current Lean files do not yet encode that source theorem at this strength:

* `SourceKummerEvaluationArrows.lean` has a reduced strip/unit interface and
  explicitly does not identify the q-pilot or construct Theorem 3.11 output;
* `SourceSHETransportLaws.lean` stores a reduced square, while the
  `SourceLocalizationExpressible` landing predicate is equivalent to
  `Nonempty Output` and has no q-mark/readout content;
* `SourceMultiradialIplLinkWiring.lean` has reduced algorithmic wiring but no
  source provenance from the actual final-evaluation family;
* `C9IUTBridgeOutput.lean` keeps q-pilot membership as an explicit
  `C1SourceBridge` field, and `C9C1IdentifiabilityProbe.lean` proves that this
  membership can coexist with a wrong volume if no readout equality is stored.

Consequently the natural-language path is complete **conditional on the
paper's xi-e/xi-f source assertion**, but an independent Lean proof still has
one exact obligation, `FinalEvaluationQMark`: for the same fixed `C`, construct
the local q-to-hull maps, the localization square, the overlap cocycle, the
effective descent into the original final-evaluation family, and the unchanged
`M`/reference/weights/readout (or instead a source-backed signed-epsilon
family). cQ3, cQ4, full-strip isomorphism, and abstract sheaf descent transport
existing arrows; none creates this marked arrow.

## Next executable package

Use one fixed admissible `C` and trace its splitting generator and `rho_v`
through the `U2 K2` IPL composite into the actual sQ3
evaluation/further-rigidification object. Record the first point at which one
of the following is absent: a local q-to-hull map, localization compatibility,
overlap cocycle, membership in the original output family, or the common
normalization. If the algorithm supplies only a collection, replace exact
attainment by a same-`C` `S_C >= kappa_C` ledger or a signed-epsilon witness.
Do not resume numerical gap tuning until this source landing is either
constructed or explicitly shown to be the missing theorem.

Validation status: natural-language source audit only; no new Lean compile,
Project build, comparator, or independent review. C1/source landing remains
open and `target_accepted=false` under the independent-Lean reading.
