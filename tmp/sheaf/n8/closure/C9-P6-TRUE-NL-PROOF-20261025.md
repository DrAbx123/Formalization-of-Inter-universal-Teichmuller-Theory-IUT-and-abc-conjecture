# C9 P6 TRUE — NATURAL-LANGUAGE PROOF RUN

Date: 2026-10-25.
Status: natural-language proof schema, no Lean, no explicit complete C.
Target: for every admissible initial Theta-data C, h_C >= Q_C.

This file is a self-contained natural-language attempt to run the P6-true
proof through IUT III Corollary 3.12. It is not a black-box citation:
the source construction-computation is written out as Lemmas A1-A3, with
the exact remaining proof obligations listed at the end.

## 0. What is being proved

P6 is the universal statement:

    for every admissible complete C,  h_C >= Q_C.                 (P6)

Here h_C is the C9 normalized log-volume of the output holomorphic hull,
and Q_C is the C9 native q calibrated global log-volume.

P6 true does NOT require constructing an explicit C. P6 false would.
The proof below is universal: it fixes an arbitrary admissible C, uses only
its initial Theta-data/q-pilot, and never chooses a concrete curve or number
field.

## 1. Notation and definitions

Let C be an admissible initial Theta-datum, in the sense of IUT I Def 3.1:
F_mod = Q, F, X_F, l=41, C_K, V, V_bad, epsilon. Fix the native q, the
BPS/Theta-gluing, the target column, and the normalization.

1.1 q-pilot object. At the Hodge theater (1,0), the q-pilot object is the
arithmetic divisor determined by the zero locus of the local q_v, v in V_bad,
in the global realified Frobenioid in the codomain of the Theta x mu
LGP-link. Its log-volume is denoted

    -|log(q)| in R.

1.2 Theta-pilot object. At (0,0), the Theta-pilot object is the arithmetic
divisor determined by the zero locus of the theta values {q_v^{j^2}},
j=1,...,l*, v in V_bad, in the global realified Frobenioid in the domain of
the Theta x mu LGP-link.

1.3 Possible images. The multiradial representation of the Theta-pilot
object produces a collection of possible images in 1,circ U, subject to the
indeterminacies (Ind1), (Ind2), (Ind3).

1.4 Holomorphic hull. Let 1,circ U be the holomorphic hull of the union of
the possible images. Its procession-normalized mono-analytic log-volume is

    -|log(Theta)| in R union {+infinity}.

1.5 C9 quantities. There are two normalizations in the C9 corpus and
they MUST NOT be conflated:

  (N) normalized convention (PaperP6 normalized target):
      h_C^norm := -|log(Theta)|,
      Q_C^norm := -|log(q)|.

  (C) canonical C9Paper convention:
      Q_C^canon := localSignedLog(qCandidate),
      h_C^canon is the corresponding canonical hull volume if used.

E15 gives the exact relation

      Q_C^canon = d * Q_C^norm,    d = [F_v:Q_p],

and in the C9 tame totally ramified type d=e=ell=41, so
Q_C^canon = 41 * Q_C^norm.

The Lean candidate target PaperP6C6AlignedTarget uses the normalized
convention (N): its qLog is Real.log ||qUnit|| and its Theta is
normalizedTheta. The C9Paper QPaper uses the canonical convention (C).
This distinction is the main target-translation issue.

## 2. Lemma T (C9 normalization identification)

Lemma T_norm. Under (N), and under the normalization identifications
(B_I-zero arch, procession average over j in F_l^*, C6 alignment), the
C9 normalized output hull volume equals the IUT III normalized hull volume
and the C9 normalized q volume equals the IUT III q-pilot volume:

    h_C^norm = -|log(Theta)|,      Q_C^norm = -|log(q)|.

Proof sketch.
(a) Both h_C^norm and -|log(Theta)| are defined as the procession-normalized
mono-analytic log-volume of the same object: the holomorphic hull of the
union of the possible images of the Theta-pilot. The procession normalization
is the average over j in F_l^*, and the B_I-zero normalization fixes the
zero of log-volume on B_I.
(b) Both Q_C^norm and -|log(q)| are the normalized log-volume of the native
q-pilot object, i.e. the arithmetic divisor of the q_v at v in V_bad.
(c) The C6 alignment identifies C6 normalizedLogVolume with the Theta
normalized log-volume; this is the C9/C6 bridge used in the Lean candidate
target. It is an identification of normalized volumes, not an additional
geometric input.

Lemma T_canon (factor d). Under (C), the same comparison gives

    Q_C^canon = d * Q_C^norm = d * (-|log(q)|),
    h_C^canon = d * (-|log(Theta)|)   if the canonical hull volume is used.

If the target mixes canonical Q with normalized h, then Cor 3.12 yields

    Q_C^canon <= d * h_C^norm,
    i.e. Q_C^canon <= 41 * h_C^norm     (C9 tame type),

NOT the canonical P6 inequality Q_C^canon <= h_C^norm. The factor is exact
(E15), not an error; it must be stated. The canonical P6 inequality follows
only after a separate normalization theorem equating the Q and h sides, or
after choosing the normalized target.

## 3. Lemma A1 (q-pilot input/representation)

Lemma A1. The q-pilot F^{value x mu}-prime-strip at (1,0) is a fixed
coric input. Its log-volume is fixed to -|log(q)| and is not subject to
(Ind1)-(Ind3). The multiradial algorithm produces possible output data in
1,circ U, linked to this input by full poly-isomorphisms of
F^{value x mu}-prime-strips: the F^{value} part is precisely a full
poly-isomorphism, while the F^{unit x mu} part is subject to (Ind1)-(Ind3).

Proof sketch (source construction).
(i) At (1,0) the q-pilot object is represented on 1,circ U_Q via the
Kummer isomorphisms and log-shells. This representation is coric: it is
the same at every vertical column, and it is rigidified by the 1-column
arithmetic holomorphic structure.
(ii) The Theta x mu LGP-link glues (0,0) to (1,0): the Theta-pilot at
(0,0) corresponds to the q-pilot at (1,0). This is the gluing isomorphism
of arithmetic holomorphic structures.
(iii) Applying the multiradial algorithm (Theorem 3.11) to the Theta-pilot
produces a collection of possible output data in 1,circ U. Each output is
linked to the q-pilot input by a full poly-isomorphism of
F^{value x mu}-prime-strips. The F^{value} portion is a full
poly-isomorphism; the F^{unit x mu} portion is subject to the three
indeterminacies.
(iv) In particular, the algorithm does not produce a new q-pilot value; it
only produces possible representations of the same fixed q-pilot input.
This is why the final comparison is tautological rather than a new
numerical computation.

Source anchors: IUT III 10166-10180, 10582-10626; IPL extraction
C9-COR312-IPL-20261025.md; APT extraction C9-COR312-APT-20261025.md.

## 4. Lemma A2 (determinant/log-volume comparison)

Lemma A2. The output data in 1,circ U, after holomorphic hull, can be
expressed via localizations of arithmetic vector bundles of rank > 1 over
the 1-column local rings. A positive tensor power of the determinant,
followed by the j-normalized log-volume, gives a quantity comparable to
the q-pilot line bundle. The two normalized log-volumes are

    -|log(Theta)|   and   -|log(q)|,

and both lie in the set

    R_{<= -|log(Theta)|} = { lambda in R | lambda <= -|log(Theta)| }.

Proof sketch.
(i) The holomorphic hull of a region is, by definition, the smallest
subset of the form lambda * O containing it, with each component of lambda
nonzero; non-relatively-compact regions are sent to IQ(-). For the
multiradial output, the hull is 1,circ U.
(ii) By Remark 3.9.5 (Ob1)-(Ob3), the hull data are represented by tensor
packets of log-shells and by localizations of arithmetic vector bundles of
rank > 1 over the 1-column local rings. The determinant of a positive
tensor power det^{tensor M} is an arithmetic line bundle; by Ob3-3, its
arithmetic degree equals the log-volume of the original vector bundle up
to the standard normalization. In particular, for the log-volume
computation, the determinant bookkeeping may be omitted.
(iii) Applying the procession-normalized log-volume (average over
j in F_l^*) to the hull gives -|log(Theta)|. Applying it to the q-pilot
line bundle gives -|log(q)|. Both are real numbers, and by construction
-|log(q)| is the fixed input value; the set R_{<= -|log(Theta)|} is the
set of possible output log-volumes.
(iv) The 1-column log-Kummer correspondence rectifies the vertical shift
between the 0-column and 1-column; this is the standard log-Kummer
rectification, not a new volume term.

Source anchors: IUT III 10641-10681, 7735-7868; Remark 3.9.5 Ob1-Ob9;
Prop 3.9.

## 5. Lemma A3 (fixed q-pilot value inclusion)

Lemma A3. By SHE, the construction is valid relative to the fixed
1-column arithmetic holomorphic structure and under the fixed input
pilot log-volume -|log(q)|. Therefore the fixed value -|log(q)| is one of
the possible output log-volumes:

    -|log(q)| in R_{<= -|log(Theta)|}.

Proof sketch.
(i) SHE (Remark 3.11.1(iii)) says that the output construction/data is
simultaneously valid relative to the domain and codomain arithmetic
holomorphic structures. It permits expressing the output relative to the
fixed 1-column local rings O_Kv, log-shells and tensor packets 1,circ U.
(ii) The permutation symmetry 0,circ U =~ 1,circ U (Theorem 3.11(i))
identifies the two columns up to a noncanonical isomorphism. The
construction is compatible with this symmetry; hence the fixed q-pilot
value is not lost when passing to the 1-column expression.
(iii) The algorithm, the hull, and the normalized log-volume therefore
produce the set of possible output log-volumes R_{<= -|log(Theta)|}, and
the fixed q-pilot value -|log(q)| belongs to this set. This is exactly the
SHE condition: the construction is valid under the fixed input volume,
not merely under some unknown value.
(iv) The inclusion is a semantic inclusion inside the multiradial
representation; it is the source's formal conclusion, not an independent
numerical computation.

Source anchors: IUT III 10682-10715; SHE extraction
C9-COR312-SHE-20261025.md; APT extraction C9-COR312-APT-20261025.md.

## 6. Main theorem (conditional natural-language P6_norm)

Theorem P6_norm. Assume Lemmas T_norm, A1, A2, A3. Then for every
admissible complete C, in the NORMALIZED convention (N),

    h_C^norm >= Q_C^norm.

Proof.
Let C be arbitrary. By A1, the q-pilot input at (1,0) is fixed and has
normalized log-volume -|log(q)|; the multiradial algorithm produces
possible output data in 1,circ U linked to this input by full
poly-isomorphisms.
By A2, after taking the holomorphic hull, the output is expressed via
rank>1 vector-bundle localizations and determinant/log-volume comparison;
the normalized log-volumes are -|log(Theta)| and -|log(q)|, and both lie
in R_{<= -|log(Theta)|}.
By A3, the fixed q-pilot value -|log(q)| belongs to
R_{<= -|log(Theta)|}. Hence

    -|log(q)| <= -|log(Theta)|.

By Lemma T_norm, Q_C^norm = -|log(q)| and h_C^norm = -|log(Theta)|.
Therefore

    Q_C^norm <= h_C^norm.

Since C was arbitrary, P6_norm holds for every admissible C. QED.

No explicit complete C is constructed at any point. The quantifier is
universal over the initial Theta-data; each C supplies its own q-pilot
input and its own multiradial representation.

IMPORTANT: This is P6 in the NORMALIZED convention (N), which is the
convention of the Lean candidate PaperP6C6AlignedTarget. It is NOT the
canonical C9Paper P6. For the canonical C9Paper target, Lemma T_canon
gives the exact factor d=41:

    Q_C^canon = 41 * Q_C^norm,
    Cor3.12 => Q_C^canon <= 41 * h_C^norm.

Thus canonical P6 (Q_canon <= h_canon) is NOT proved by this run unless a
separate normalization theorem equates the canonical Q and h sides. The
normalized P6 and canonical P6 are different targets; they must not be
conflated.

## 7. Why this is not a black-box citation

The proof uses only:
- the definition of the q-pilot and Theta-pilot;
- the multiradial algorithm/Theorem 3.11 and its IPL/SHE/APT invariants;
- the holomorphic hull and Remark 3.9.5 Ob1-Ob9;
- the procession-normalized log-volume and Prop 3.9;
- the fixed q-pilot input and SHE;
- the normalization identification T.

Each source input is named with its exact role. The proof does not quote
Cor 3.12 as an oracle; it reproduces the construction-computation that
yields the inequality. What remains is to expand the named source inputs
into complete proofs (see Section 8).

## 8. Exact remaining proof obligations

To make the above unconditional and black-box-free, the following must be
proved/formalized, not assumed:

M1. xi-f inclusion: the precise set-membership
    -|log(q)| in R_{<= -|log(Theta)|}, including the "perhaps up to
    approximation" wording.
M2. Determinant exponent and normalized log-volume comparison: display the
    positive tensor power det^{tensor M}, the O(-) adjustment, and the
    equality of arithmetic degree and log-volume.
M3. SHE equivalence: the exact sense in which the output construction is
    valid relative to the fixed 1-column structure.
M4. Ind3 direction: the compatibility of the Kummer-detachment/Ind3
    indeterminacy with the log-volume comparison.
M5. 1-column log-Kummer rectification: the vertical shift rectification.
M6. Upstream O1-O7: Theorem 3.11(i)-(ii), Prop 3.9, Remark 3.9.5,
    hull existence/compactness/log-volume finiteness.
M7. IUT IV/C9 bridge and normalization T: canonical/normalized factor d,
    B_I-zero, procession average, C6 alignment.

These are proof obligations inside the source construction. None of them
requires constructing an explicit complete C. They are exactly the
obligations that the Cor3.12 natural-language extraction has isolated.

## 9. Relation to the counterexample route

P6 false would require an explicit admissible complete C with h_C < Q_C.
That would require constructing the global BPS/0-column/target/arch data
and verifying JP/G1/U etc. It is a different, existential route.

P6 true, in contrast, is the universal inequality. The proof above does
not construct C; it proves the inequality for an arbitrary fixed C from
the source construction. This is why the P6-true route is conceptually
simpler than the counterexample route, even though its source proof is
long.

## 10. Status

P6 true: reduced to T + A1 + A2 + A3 (Lemmas), with obligations M1-M7.
P6 false: not established.
P6: OPEN.
No Lean; no explicit complete C; no black box accepted as an axiom.
target_accepted = false.
