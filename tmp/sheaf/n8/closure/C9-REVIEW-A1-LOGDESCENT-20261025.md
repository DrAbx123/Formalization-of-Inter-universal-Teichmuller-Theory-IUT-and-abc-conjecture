# C9 review A1: q-pilot/source input

Task: task-412 (C9-REVIEW-A1-LOGDESCENT-20261025). Owner: logdescent. Date: 2026-10-25. Review only; no rewrite; uniform scope; no mixed/E3; only this file written; no Lean/Project/target/other-owner edits; no arbitrary. P6 open.

Reviewed files/claims:
- C9-CAN-A1-20261025.md (task-407), especially (1.1), Theorem A1 canonical, (3.1)-(3.2).
- C9-SMOOTH-A1-20261025.md (task-398), especially Smooth A1 (2.1), 3.1-3.4, (4.1).
- C9-P6NORM-A1-20261025.md (task-384), especially A1.1-A1.4.
- C9-P6NORM-QVALUE-20261025.md (task-390), especially (1.1), (3.1)-(3.2), section 5 gap.
- C9-THETA-ROOT-CANONICAL-20261025.md (task-294), relative root/root-rotation.

Source checked: IUT III sources/IUT-III.txt, Definition 3.8(i),(ii) lines 6506-6590; Remark 3.11.1(ii),(iii) lines 9479-9582; Theorem B lines 1155-1184; Step (xi-a)-(xi-c) lines 10570-10649; xi-e lines 10682-10704.

## 0. Verdict

A1 is ACCEPTED at the **object/class level**, with three corrections:
1. The q-pilot input is the fixed/coric q-pilot F^value×mu-prime-strip **in the codomain (1,0)**, not a q-pilot object on the 0-column. The 0-column supplies the Theta-pilot/vertically coric arithmetic structure and log-Kummer data; the q-pilot is the codomain input. Reject q-pilot-on-0-column wording.
2. Q_can=-|log q| is ACCEPTED as source **notation/object-level** log-volume, but the numerical 82-root formula -|log q|=-(1/82)v_p(q_v)logp=-(b/41)logp is NOT an IUT III theorem; it is a C9/TAME normalization. The numerical value is CONDITIONAL on that normalization, not source-exact.
3. The full-poly class is ACCEPTED, but it must be identified as the class of the **codomain q-pilot F^value×mu-prime-strip**, not as the full LGP-link including the domain Theta-pilot side; and full-poly invariance of the canonical log-volume is a source-expansion lemma (Prop3.9(i),(ii)), not a separately displayed A1 sentence.

The remaining A1 gaps are: no canonical q_v/generator, no chosen BPS representative, no concrete global BPS/0-column/target data, and the exact numerical normalization gap. These are correctly marked in the reviewed files; the review rejects only the source-exactness of the numerical q-value and the q-pilot-on-0-column wording.

## 1. Step-by-step review

### A1.1 Full poly-isomorphism class

Claim: A1 uses the full poly-isomorphism class [F^value×mu] of F^value×mu-prime-strips, no representative (CAN-A1 (1.1)(1); SMOOTH-A1 (2.1)).

Source: Definition 3.8(ii) lines 6566-6590: the Theta×mu LGP-link is the full poly-isomorphism of F^value×mu-prime-strips F_LGP ~> F_Delta. It is a full poly-isomorphism, not a chosen map.

Verdict: ACCEPT with specification.
- The class must be that of the **codomain q-pilot F^value×mu-prime-strip** F_Delta (the fixed/coric input of Remark3.11.1(ii)), or of prime-strips full-poly-isomorphic to it. It is not the class of the whole LGP-link object including the domain Theta-pilot side.
- No representative is required for log-volume comparisons; a representative would be an arbitrary choice. This is correct.
- The phrase "participating in the LGP-link" in CAN-A1 (1.1)(1) is ambiguous: the link has two sides. It should say "the codomain q-pilot side, up to full poly-isomorphism." Not a mathematical error, but a precision correction.

### A1.2 Q_pilot up to torsion

Claim: Q_pilot is the q-pilot object of the global realified Frobenioid C^⊩_Delta determined by any collection, indexed by v in Vbad, of generators up to torsion of the splitting monoids; equivalently by q_v up to torsion (CAN-A1 (1.1)(2), Theorem A1(a); SMOOTH-A1 3.1).

Source: Definition 3.8(i) lines 6528-6544: the q-pilot object is the object of the global realified Frobenioid determined by any collection of generators up to torsion of the splitting monoid associated to the split Frobenioid; concretely, by the q_v at v in Vbad.

Verdict: ACCEPT.
- The source explicitly says "any collection ... of generators up to torsion"; the object is determined by such a collection.
- q_v itself is not canonical; Q_pilot is the canonical object. The claim "up to torsion" should be attached to the **generator collection**, not to Q_pilot as an object with an extra torsion ambiguity. The reviewed files do this in substance; wording correction only.
- No canonical scalar q_v is required; this is not a gap.

### A1.3 Q_can=-|log q| at object/notation level

Claim: Q_can=-|log q| is the canonical packet+procession-normalized log-volume of Q_pilot, a full-poly-invariant paper object, not a normalized surrogate (CAN-A1 (1.1)(3),(3.2); SMOOTH-A1 (4.1)).

Source: Theorem B lines 1155-1184 defines -|log q| as the procession-normalized mono-analytic log-volume of the image of a q-pilot object in the multiradial representation, which is not subject to (Ind1)-(Ind3). The notation is source-defined. Prop3.9(i) lines 6755-6778 defines packet-normalization and procession-normalization.

Verdict: ACCEPT at notation/object level, with a precision correction:
- The source's -|log q| is the log-volume of the **image of the q-pilot object in the multiradial representation on 1,circU_Q**, not simply the log-volume of the abstract object Q_pilot in C^⊩_Delta. The reviewed files often identify these. The identification is part of A1 representation/xi-a-c, but it should be stated explicitly.
- The value is canonical only after the packet+procession normalization and after the full-poly-invariance lemma (L1); the latter is a source expansion from Prop3.9(i),(ii), not an isolated A1 theorem.
- No normalized Q_norm/h_C surrogate is used; CAN-A1 correctly excludes that.

### A1.4 Numerical q-pilot value and 82-root normalization

Claim: Q_can=-|log q|=-(1/82)v_p(q_v)logp=-(b/41)logp, with q_v=p^{2b}u, qhat=q_v^{1/82}=pi^b v, root/unit independent (QVALUE (1.1),(3.1)-(3.2); cited as fixing A1/A3 numeric value).

Source: IUT III defines Q_pilot and -|log q|, but does **not** state the local formula -(1/82)v_p(q_v)logp or the 82-root decomposition. The local E_j facts v_p(q)=2b, qhat=pi^b v, v_pi(qhat)=b are C9/TAME local arithmetic; the normalized readout is a C9 normalization (QVALUE section 5 explicitly records this as the exact gap).

Verdict: CONDITIONAL / NOT SOURCE-EXACT.
- The local algebra q=p^{2b}u, qhat=q^{1/82}=pi^b v, v_p(qhat)=b/41, root/unit independence is ACCEPTED as C9/TAME local input (actual E_j data).
- The equality Q_can=-(b/41)logp is ACCEPTED only **relative to the C9/TAME packet-normalization convention**; it is not an IUT III numerical theorem. QVALUE itself says this (lines 118-131). Therefore A1 cannot claim the numerical q-value as source-exact; it must carry the normalization hypothesis explicitly.
- The 82-root ambiguity is correctly handled: qhat is only relative to a uniformizer, roots form a mu_82-torsor, root rotation zeta with zeta_j -> zeta^{-j^2}zeta_j leaves the physical g_j profile invariant (THETA-ROOT-CANONICAL Theorem, lines 43-57). ACCEPT this root-rotation statement. But "canonical Q_can" at the numerical level is canonical only after the normalization/root-rotation equivalence is fixed; no absolute canonical root is determined by E_546.
- Reject any statement that IUT III itself fixes the 82-root/valuation normalization; accept it as an exact C9 normalization choice, not arbitrary.

### A1.5 0-column data

Claim: A1 includes Z_0, the 0-column data: vertical line n=0 with q-pilot/Theta-pilot and LGP-gluing (CAN-A1 (1.1)(4), Theorem A1(d)); SMOOTH-A1 3.4 says 0-column is vertical line n=0 with (0,circ) structures from unit portion/bi-coricity/log-Kummer.

Source: Cor3.12 Steps (iii)-(v) lines 10309-10368: one works on the 0-column with vertically coric structures invariant under vertical shifts, related to Frobenius-like structures by log-Kummer; the q-pilot is at (1,0); the Theta-pilot is at (0,0); the LGP-link goes (0,0)->(1,0). xi-a lines 10571-10581: q-pilot object at (1,0).

Verdict: ACCEPT 0-column as source-defined arithmetic structure/log-Kummer data; REJECT "q-pilot on the 0-column" if intended literally.
- The 0-column carries the Theta-pilot and the vertically coric arithmetic holomorphic structure; the q-pilot object is the codomain (1,0) input. The q-pilot F^value×mu-prime-strip is fixed/coric as the codomain input (Remark3.11.1(ii)).
- Z_0 should be described as: vertical line n=0 with its vertically coric structures, Theta-pilot side, and the LGP-link data to the 1-column; the q-pilot is the 1-column codomain input, not an object "on the 0-column".
- This is a correction of wording/object placement, not a rejection of the 0-column's role.

### A1.6 BPS representative / no canonical section

Claim: no canonical BPS representative; A1 uses the full-poly class; no canonical q_v or section (CAN-A1 section 4; SMOOTH-A1 3.2/3.3).

Verdict: ACCEPT.
- The source input is a full poly-isomorphism class/object determined up to torsion; choosing a representative would be arbitrary.
- The output is a collection of possibilities, not a section; A1 supplies the fixed q-pilot value as an element/input, not a section of the output family.
- Concrete global BPS/0-column/target data remain missing; this is a concrete-instantiation gap, not an A1 canonicality gap. Correctly marked.

## 2. Exact accepted A1 statement (review form)

The following is accepted as source-exact at object/class level:

    A1_obj = ( codomain q-pilot full-poly class [F^value×mu],
               q-pilot object Q_pilot determined by generators up to torsion,
               source notation Q_can=-|log q|,
               0-column vertically coric arithmetic structure/log-Kummer data,
               full-poly IPL link to output data ).

The following is accepted only conditionally:

    Q_can numeric = -(b/41)logp  (b=3,273), under the C9/TAME
    packet+procession normalization and the 82-root/valuation convention.

The following is rejected as source-exact:

    "q-pilot object on the 0-column" (the q-pilot is the codomain (1,0) input);
    "IUT III states Q_can=-(1/82)v_p(q_v)logp" (C9 normalization, not source theorem);
    "canonical absolute 82nd root qhat" (only relative to a uniformizer; root rotation equivalence).

## 3. Reasons/gaps

R1 (accepted class): Definition3.8(ii) full poly-isomorphism; no chosen representative. Correct.
R2 (accepted object): Definition3.8(i) generators up to torsion; Q_pilot object. Correct; wording "Q_pilot up to torsion" should be "generators up to torsion."
R3 (accepted notation): Theorem B -|log q|; but it is the image in the multiradial representation, not just the abstract object. State the representation link.
R4 (conditional value): QVALUE section 5 exact gap: local formula is C9/TAME normalization, not IUT III. The numerical value cannot be used as source-exact A1.
R5 (0-column correction): q-pilot at (1,0); 0-column has Theta-pilot/vertically coric structure. Correct the object placement.
R6 (BPS/class): no canonical BPS representative; full-poly class and no section accepted. Concrete global BPS/0-column/target missing.
R7 (root): mu_82 torsor/relative root; root rotation absorbed; no absolute root. Accepted.

## 4. Consequence for P6_can

A1 at object/class level is source-exact and can feed A2/A3: the q-pilot input is fixed/coric, the output is linked by full poly-isomorphism, and Q_can is source notation for the canonical log-volume. The numerical value -(b/41)logp is a C9-normalized evaluation and must be carried as a hypothesis, not attributed to IUT III. The q-pilot-on-0-column wording must be corrected before the A1 -> A2/A3 chain is used in a formal proof.

No rewrite of the reviewed files is performed; this is an accept/reject review. No normalized surrogate, no mixed/E3, no Lean.

## 5. Verdict summary

| Step | Verdict |
|---|---|
| Full-poly class | ACCEPT with codomain specification |
| Q_pilot generators up to torsion | ACCEPT (wording: generators, not object) |
| Q_can=-|log q| notation/object | ACCEPT with representation link |
| Q_can=-(b/41)logp numerical 82-root | CONDITIONAL on C9 normalization; NOT source-exact |
| qhat root/root rotation | ACCEPT relative/canonical up to mu_82; no absolute root |
| 0-column | ACCEPT arithmetic/Theta-pilot/log-Kummer; REJECT q-pilot-on-0-column wording |
| BPS representative/no section | ACCEPT |
| concrete E_546 A1/0-column/target | MISSING concrete instantiation, correctly marked |

Only C9-REVIEW-A1-LOGDESCENT-20261025.md written. No Lean/Project edits. target_accepted=false; P6 open.
