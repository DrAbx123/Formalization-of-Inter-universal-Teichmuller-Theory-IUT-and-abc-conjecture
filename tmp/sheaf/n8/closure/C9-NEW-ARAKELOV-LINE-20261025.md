# C9 new-math program: Arakelov Theta-pilot line bundle

Task: task-243. Date: 2026-10-25. Author: transport.
Stage: exploratory natural-language construction and theorem attempt. No Lean,
no Project/target edits. Only this file written. target_accepted=false.

## 0. Executive verdict

The program as literally stated has a SIGN problem:

    if deg(L)=Q_C-h_C and L has a nonzero effective section,
    then deg(L)>=0 gives Q_C>=h_C,

which is the OPPOSITE of the desired P6 inequality h_C>=Q_C. A nonzero
effective section of a line bundle of degree Q_C-h_C cannot prove
Q_C<=h_C.

The corrected orientation is

    L_C := M_C tensor N_C^{-1},
    deg(M_C)=h_C,  deg(N_C)=Q_C,
    deg(L_C)=h_C-Q_C.                                      (0.1)

A nonzero effective/positive section of this L_C would give h_C>=Q_C.

The construction of L_C from BPS/Theta-gluing is a coherent conditional
program, but the current source does not supply:

- a complete C with the needed compactification;
- canonical Hermitian metrics with the required normalizations;
- a nonzero theta section of L_C with controlled norms/effectivity;
- a proof that the section's degree is the required log-volume difference.

So the program is not a current theorem. It is a conditional route whose
central section/positivity step is essentially equivalent to the desired
inequality, not a bypass of TC or of the missing complete C. It does avoid the
H_A/B branch in its formulation, which is a genuine conceptual advantage.

## 1. Data and desired inequality

Fix a complete admissible source configuration C with:

- native q-pilot and BPS/Theta-gluing;
- target hull H_C and its normalized log-volume h_C=nu(H_C);
- native q calibrated log-volume Q_C;
- fixed normalization and target column.

P6 is

    h_C >= Q_C.                                             (1.1)

An Arakelov line bundle proof would construct a Hermitian line bundle L_C on
the compactified curve/stack with

    deg_hat(L_C) = h_C - Q_C,                               (1.2)

and prove L_C is effective/nef/positive, hence deg_hat(L_C)>=0, giving (1.1).

The phrase "Arakelov degree" here means the adelic arithmetic degree:
finite log-volumes plus archimedean log-volumes, normalized by the degree of
the base field.

## 2. Sign lemma

Lemma 2.1 (orientation). Let L be a Hermitian line bundle on the arithmetic
curve with a nonzero global section s whose divisor is effective and whose
adelic norm is at most 1 at every place (or whose metric is nef/semipositive
in the sense needed for the degree inequality).

(a) If deg(L)=h_C-Q_C, then deg(L)>=0 gives h_C>=Q_C.
(b) If deg(L)=Q_C-h_C, then deg(L)>=0 gives Q_C>=h_C, not the desired P6.
(c) Therefore the task as stated with degree Q_C-h_C and a positive/effective
    section proves the wrong inequality.

Proof. (a),(b) are immediate from the sign of the degree. (c) follows by
applying (b). QED.

Remark 2.2. A nonzero global section alone does not imply a nonnegative
Arakelov degree without a metric/norm control: rescaling the metric changes
the degree. The program must include a canonical metric normalization and a
small/effective section, not merely an algebraic section. This is a second
gap beyond the sign.

## 3. Candidate construction

### 3.1 The two basic bundles

Assume the following source objects exist:

(A1) a Hermitian line bundle N_C on the compactified C whose arithmetic degree
     is Q_C and whose metric is determined by the native q/BPS data;

(A2) a Hermitian line bundle M_C whose arithmetic degree is h_C and whose
     metric is the Theta/Hodge L2 metric determined by the target hull H_C;

(A3) both metrics are fixed by the BPS/Theta gluing and the chosen
     normalization, with no arbitrary scaling.

Then define the corrected Arakelov Theta-pilot bundle

    L_C := M_C tensor N_C^{-1}.                             (3.1)

Its degree is

    deg_hat(L_C)=h_C-Q_C.                                   (3.2)

This is independent of the H_A/B branch as a formal construction: it uses the
target hull and the native q/BPS data, not U or a B=O_K/B=I choice.

The "Theta-pilot section" would be a nonzero section

    s_theta in H^0(C,L_C)                                  (3.3)

obtained by dividing the Theta/Hodge section by the q-pilot section. Its zero
divisor should be the effective difference of the hull divisor and the
q-pilot divisor. This is the central object; its existence is not automatic
and is not supplied by the current source.

### 3.2 Metrics from BPS/Theta gluing

The intended metric on L_C is the quotient of the M_C Theta metric by the
N_C BPS metric:

    ||s_theta|| = ||s_M|| / ||s_N||.                       (3.4)

The gluing data must ensure that the local norms glue to an adelic metric and
that the resulting Arakelov degree is exactly the normalized log-volume
difference. This is a condition, not a consequence of the word "gluing":
BPS/Theta gluing gives transition and local volume data, not a canonical
global section.

### 3.3 Effectivity/positivity

If s_theta is nonzero and its adelic norm is at most 1, and if the metric has
nonnegative curvature/nef behavior, then

    deg_hat(L_C) >= 0,                                      (3.5)
    h_C >= Q_C.                                             (3.6)

This is the desired conclusion.

## 4. Conditional theorem

Theorem 4.1 (conditional Arakelov route). Assume:

(A1)-(A3) above;

(A4) the quotient metric on L_C is the canonical BPS/Theta adelic metric, with
     no arbitrary scaling, and its degree is h_C-Q_C;

(A5) L_C has a nonzero theta section s_theta whose zero divisor is effective
     and whose adelic norm is at most 1, or equivalently L_C is effective/nef/
     positive in the Arakelov sense;

(A6) the BPS/Theta gluing identifies the section divisor with the hull
     difference and preserves the normalization.

Then h_C>=Q_C.

Proof. By (A4), deg L_C=h_C-Q_C. By (A5), the nonzero effective/nef section
gives deg L_C>=0. Hence h_C-Q_C>=0. QED.

Status: this is a valid conditional theorem. It is not a proof of P6, because
A1-A6 are not constructed in the frozen corpus. In particular, A5 is
essentially the geometric heart of the desired inequality; it cannot be
obtained from the BPS/Theta gluing alone without a positivity theorem.

## 5. Is the program independent of H_A/B?

Formally, yes: L_C is defined from M_C,N_C, target hull, q/BPS data. No U=<y1>,
no B=O_K/B=I branch appears. This is the conceptual advantage of the program.

But independence of H_A/B does not remove the other missing layers:

1. Complete C/compactification: the current source has no explicit complete
   C with all IUT I Def3.1 data and target column. A line bundle on a
   nonexistent curve is only a formal symbol.
2. Target hull H_C and h_C: constructing M_C with degree h_C requires the
   actual hull/its divisor and TC-A..TC-H/TC-S. The B branch is not the only
   obstruction.
3. Canonical metrics: BPS/Theta gluing may fix local metrics up to constants;
   the global normalization of an Arakelov metric is not automatic. An
   arbitrary scaling changes deg L_C and can make any sign. A no-arbitrary-
   metric theorem is missing.
4. Theta section: existence of a nonzero section of L_C with controlled norm
   is not implied by the existence of BPS/Theta gluing data. It is a
   positivity statement at least as strong as the desired inequality.
5. H_A/B: even if L_C avoids the branch, the finite q-pilot data may enter
   N_C; if N_C is defined through the q-pilot region, the branch type-gap
   could reappear. The construction must specify N_C without U/B.

Thus the program is B-independent only in its formal orientation; it is not a
B-independent proof of P6.

## 6. No-go from current source

The following are proved or follow from the current corpus:

(N1) SIGN: as stated, deg=Q_C-h_C plus effective/positive cannot give
     Q_C<=h_C. The correct sign is h_C-Q_C.

(N2) A nonzero algebraic section alone is insufficient without a metric/norm
     normalization; arbitrary metric scaling changes the Arakelov degree.

(N3) The current source does not construct the complete C, the compactified
     arithmetic curve, the Hermitian bundles M_C,N_C, or their adelic metrics
     with the required normalization.

(N4) The BPS/Theta gluing data do not by themselves produce a nonzero global
     theta section of L_C; assuming one with controlled norm is equivalent to
     assuming the desired positivity.

(N5) Even granting H_A/B independence, TC-A..TC-H/TC-S, the actual archimedean
     hull, and the fixed q/Theta target class remain missing.

Consequently the program cannot be run as an unconditional proof from the
current frozen corpus. It is a promising organizing framework, not a theorem.

## 7. Possible repairs and next executable steps

To turn the program into a theorem one would need at least one of:

1. A construction of the compactified arithmetic curve/stack C with its
   BPS/Theta model and canonical adelic metrics, independent of U/B.
2. A canonical theta section of L_C whose zero divisor is the hull-q divisor,
   with a proof of norm<=1/effectivity from BPS/Theta positivity.
3. An identification deg_hat(L_C)=h_C-Q_C as a theorem, not a definition,
   including the archimedean normalization (B_I-zero) and finite weights.
4. A proof that the construction is invariant under the H_A/B choices, or a
   proof that those choices do not enter N_C.
5. A direct computation of the section divisor on an actual C; this is
   essentially the missing P6 content.

Absent these, the Arakelov route is conditional and circular at the
positivity/section step.

## 8. Status classification

PROVED IN THIS NOTE:

- sign Lemma 2.1: Q_C-h_C plus positive/effective proves the wrong inequality;
- corrected orientation L_C=M_C tensor N_C^{-1} has degree h_C-Q_C;
- conditional theorem 4.1.

CONDITIONAL/ASSUMED:

- existence of M_C,N_C with canonical BPS/Theta metrics and degrees h_C,Q_C;
- existence of nonzero effective/nef theta section;
- identification of its divisor/degree with the hull-q difference;
- BPS/Theta gluing compatibility and archimedean normalization.

MISSING FROM CURRENT SOURCE:

- complete C/compactification; explicit M_C,N_C; metrics; section;
- TC-A..TC-H/TC-S; actual h_C/Q_C data; H_A/B independence proof;
- any unconditional P6 conclusion.

## 9. Conclusion

The Arakelov Theta-pilot line bundle is a natural formal route to P6:

    L_C = M_C tensor N_C^{-1},   deg L_C=h_C-Q_C,
    nonzero effective/nef theta section => h_C>=Q_C.

It avoids U/B in its orientation and is worth developing. But the literal
version with degree Q_C-h_C proves the opposite inequality, and the corrected
version is conditional on a complete C, canonical metrics, and a theta section
whose existence is essentially the desired positivity. No unconditional proof
or contradiction follows from the current corpus.

target_accepted=false.
