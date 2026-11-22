# C9 independent review of P6_can natural-language proof

Task: task-408. Reviewer: kummer. Date: 2026-10-25.
Review only; do not rewrite; no Lean/Project edits; no mixed/E3.
Only this file written. target_accepted=false; P6 open.

## 0. Reviewed file

- C9-P6-CAN-NATURAL-PROOF-20261025.md, 162 lines,
  SHA256 e78bad81b1abe4cd365d77391888c7b4dc74a3b3cc4e5fc83e8f21eb7b58a1c9.
- Cross-check: C9-P6-CAN-CHAIN-20261025.md, 109 lines,
  SHA256 042f309285840f3cf60d05bd49e88d1a6280aa66ad15fbbdb91e5abdba3ff5da.
- IUT III source text, SHA256
  822e03da7e2a7402a3bb406d698bb3374401e3fb102058c80864d6c06139353d.

Proof target: paper P6_can = for every admissible initial Theta-data C,
Q_can(C) <= h_can(C), Q_can=-|log q|, h_can=-|log Theta|.

## 1. Verdict

**REJECT the proof as a complete proof of P6_can.** It is a coherent
**conditional schema**, not a finished natural-language proof.

Accept:

- A1 as a source-conditional input lemma, with a small well-definedness caveat.
- T_can only as a **definitional instantiation** of the paper target, not as a
  theorem identifying an independently defined C9 target.

Reject:

- A2 as an exact determinant/log-volume identity: it omits the open G1-G7
  determinant/localization/hull/log-Kummer steps and asserts the conclusion.
- A3 as exact membership Q_can in R_{<=h_can}: the source explicitly allows
  only "perhaps only up to some sort of approximation"; the proof has no error
  term and cannot assert exact inclusion.
- The final Theorem as unconditional: P6_can follows only if A2 and A3 are
  exact, which they are not in this proof.

## 2. Lemma A1: ACCEPT with caveat

Proof lines 34-48. Contents:

- q-pilot C^value x mu prime-strip is fixed/coric input;
- canonical log-volume Q_can=-|log q|, not subject to Ind1/2/3;
- output linked by full poly-isomorphisms: F^value full polyiso, F^unit x mu
  Ind1/2/3.

Assessment:

- Def3.8(i) supports the q-pilot object from q_v up to torsion.
- Rem3.11.1(ii)/(iii) supports the coric/fixed F^value x mu input and IPL.
- Def3.8(ii) supports the LGP-link full poly-isomorphism.
- The F^value/F^unit x mu split is source-extracted (task-372).

Caveat: the proof asserts without expansion that Q_can is independent of the
generator collection and full-poly representative. Def3.8(i) says the object
is determined by any collection up to torsion, but the log-volume invariance
under all full-poly representatives is not proved line by line. This is a
minor well-definedness gap, not a wrong inference.

Verdict: ACCEPT conditional on Def3.8(i)/Rem3.11.1; not a black box after
task-372/384 expansion.

## 3. Lemma A2: REJECT as exact

Proof lines 52-72. It defines an arithmetic vector bundle E_H of rank>1,
L_H=det^tensor M(E_H) tensor det^tensor M(O(-))^{-1}, and asserts:

    deg(L_H)/M = deg(det E_H) = mu_log(H(C)) = h_can,
    deg(L_q)=Q_can.

Problems:

1. E_H is not explicitly constructed. The proof says "let E_H be this bundle"
   from Ob1-Ob2; source only gives the representation via localizations of
   arithmetic vector bundles, not a specific E_H for the target hull.
2. The det^tensor M/O(-) adjustment is not proved degree zero. The proof says
   Prop3.9(i) gives deg(O(-))=0 and therefore the O(-) adjustment has degree
   zero. That is not an explicit source computation; Ob3-2 defines the
   normalization by the inverse determinant of O(-), and its determinant/
   degree bookkeeping is not shown.
3. The factor M and the division by M are asserted to cancel; the source
   weights N_v/M and the positive tensor power convention are not derived.
4. The hull approximant phi(P) versus H_Phi(P), vertical shift/log-Kummer
   adjustment, and tensor-twist/upper-semi compatibility are not treated.
   The proof jumps from Ob3 to mu_log(H(C)).

This is not a harmless omission: the proof's own chain file
C9-P6-CAN-CHAIN lines 41-46 and 94-100 lists A2-G1..G7 as open source gaps
(explicit E_H/determinant, O(-), M, weights, hull approximant, vertical shift,
tensor twist). The natural proof does not close them; it restates the desired
equality. Therefore A2 is a **conditional identity**, not a proved exact step.

Verdict: REJECT as exact. ACCEPT only conditional on A2-G1..G7.

## 4. Lemma A3: REJECT as exact

Proof lines 76-127. It claims Q_can in R_{<=h_can} via:

1. formal quotient (Ob9-1/Ob4-3/Ob5/Ob8);
2. sQ3/sQ4 compatibility;
3. closed loop of F^value x mu prime-strips;
4. simultaneous q-intertwining AND Theta-intertwining;
5. apply sQ5/log-volume and conclude Q_can is a projection/special case of
   Theta-pilot output log-volume, hence Q_can in R_{<=h_can}.

Problems:

1. **Exact membership is not source-exact.** IUT III proof of Cor3.12,
   lines 10708-10710, says the construction of output possibilities
   constitutes a construction of the pilot-object log-volume of the input
   "perhaps only up to some sort of approximation, as a result of various
   indeterminacies". The natural proof line 155 explicitly says "No numerical
   epsilon: A3 uses the formal quotient/indeterminacies, not an unknown
   error." That directly contradicts the source's approximation caveat. The
   formal quotient does not automatically make an approximate construction
   exact; that would need a separate theorem (error zero / exact
   cancellation), which is not supplied.
2. **The closed loop proves simultaneous intertwinings, not inclusion.**
   The source lines 10708-10715 give the inclusion only after the construction
   constitutes the q-pilot log-volume. The proof's step 5 asserts "the q-pilot
   log-volume is the projection/special case of the Theta-pilot output
   log-volume under the same indeterminacy quotient" without a source step
   establishing that identification. Simultaneous q- and Theta-intertwinings
   on one prime-strip do not by themselves say Q_can is an element of the
   output log-volume set R_{<=h_can}.
3. **The AND/subquotient step is formal but does not produce a numerical
   inequality.** The proof calls the second arrow purely formal, then uses it
   to transfer the q-intertwining into the Theta-intertwining output set.
   This is the key unproved bridge; the source gives the inclusion via
   Steps (xi-d)-(xi-f), not via the AND alone.
4. The proof's own chain file lines 48-54 marks A3-G1 as the open
   approximation gap. The natural proof ignores that named gap.

Verdict: REJECT as exact membership. ACCEPT only as a conditional schema with
an explicit approximation/error term (or an additional source theorem that the
approximation is exact).

## 5. Lemma T_can: ACCEPT definitional only; REJECT as a theorem

Proof lines 131-136 say C9Hull=IIIHull and C9QPilot=IIIQPilot are "the
definition of the paper target, not an additional theorem."

Assessment:

- Within this proof, QP(C) and H(C) are themselves defined as the source
  q-pilot/hull objects (lines 22-30). So under that definition T_can is
  definitional; no circularity if the paper target is defined that way.
- However, T_can as an **object identity theorem** for independently defined
  C9Hull/C9QPilot is not proved. Task-403 established the exact gap
  TG1-TG3: C9 target/native objects are not identified with the source objects
  by IUT III. The proof cannot claim both "definitional" and "proved object
  identity".
- If the proof's target is paper P6_can and the objects are defined as source
  objects, T_can is acceptable as a definition. If the target is a C9 target
  with abstract H_C/native q, T_can is a gap.

Verdict: ACCEPT definitional branch; REJECT any claim that T_can is a proved
object identity for C9 target objects.

## 6. Final theorem: REJECT unconditional

Proof lines 140-146: for every admissible C, Q_can<=h_can.

The final step uses A2 exact and A3 exact. Since both are rejected as exact,
the theorem is only conditional on:

- A2-G1..G7 determinant/log-volume identity;
- A3 exact membership or an explicit approximation error integrable to zero
  (or an additional exactness theorem);
- T_can definitional target choice.

Without those, the proof is a conditional schema. It does not establish
P6_can as a completed proof.

## 7. Other exact issues

1. **"No normalized surrogate" is respected**, but the proof's A2/A3 still use
   the common packet+procession normalization; that is the paper normalization,
   not the C6 finite-block normalization. This part is internally consistent.
2. **No factor 41** claim: the proof does not explicitly insert 41 in A2/A3;
   however, A2's det^tensor M/O(-) bookkeeping could hide a normalization
   factor if M or O(-) is not derived. The proof should not claim "no factor"
   until G1-G7 are closed.
3. **Universal quantifier**: the proof argues for arbitrary admissible C, but
   A2/A3 are source-construction statements for every C; conditional on them,
   universality is formal. Fine.
4. **No explicit complete C** is needed if A1-A3/T_can are source-universal;
   this is consistent.
5. **No black box**: A1 is expanded by task-372/384, but A2/A3 are not;
   citing Ob1-Ob9 without closing the named gaps is effectively a black-box
   step.

## 8. Per-lemma review table

| item | verdict | exact reason |
|---|---|---|
| A1 q-pilot input | ACCEPT conditional | Def3.8(i)/Rem3.11.1 support it; Q_can full-poly invariance needs a line-by-line proof |
| A2 determinant/log-volume | REJECT as exact | G1-G7 open: E_H, O(-), M, weights, hull approximant, vertical shift, tensor twist |
| A3 membership | REJECT as exact | IUT III allows "perhaps approximation"; no error term/exactness theorem; closed loop != inclusion |
| T_can object identity | ACCEPT definitional only | C9 objects defined as source in this proof; as a theorem for abstract C9 target, task-403 gap TG1-TG3 |
| Final P6_can theorem | REJECT unconditional | depends on rejected exact A2/A3 |
| P6_can conditional schema | ACCEPT with named gaps | A1 + T_can-definitional + A2-G1..G7 + A3 exact/error theorem |

## 9. Conclusion

The P6_can natural-language proof is not accepted as complete. Its A1 is
source-conditionally sound, and its T_can is acceptable only as a definitional
choice of target. A2 and A3 are exactly the source comparison steps that the
C9 chain file itself lists as open (A2-G1..G7 and A3-G1); the natural proof
restates their conclusions without closing them. In particular, the source's
"perhaps only up to some sort of approximation" for A3 cannot be replaced by
"no numerical epsilon" without a new exactness theorem. Therefore P6_can is
**not proved unconditionally**; it is conditional on A2-G1..G7, A3 exact
membership/error control, and the T_can definitional target choice.

No rewrite of the proof is made; no mixed/E3; no Lean/kernel closure;
target_accepted=false; P6 open.

## 10. Status

- Independent review only; no Lean/Project edits.
- A1 accept conditional; A2/A3 reject as exact; T_can definitional only;
  final P6_can reject unconditional.
- target_accepted=false.
