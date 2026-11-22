# C9 Cor3.12 target translation: h_C = -|log Theta|, Q_C = -|log q|

Task: task-380 (decisive target translation). Owner: qside. Date: 2026-10-25.
Natural-language theorem/gap audit; no black box; no mixed/E3; no Lean/Project
edits; only this file written.

## 0. Verdict

The translation

    T:  h_C = -|log(Theta)|,      Q_C = -|log(q)|

is the exact C9-specific identification required to apply IUT III Corollary
3.12 to P6.  It is a statement about normalized log-volume functionals, not
about constructing an explicit complete C.

Conditional theorem (valid):

    If T holds as an identity of normalized log-volume functionals, then
    Corollary 3.12 (A1-A3) gives, for every admissible fixed initial
    Theta-data/q-pilot input,

        -|log(q)| <= -|log(Theta)|,
        Q_C <= h_C,
        P6 true.

No explicit complete C is constructed or needed.  P6 is universal; P6-true
does not require an explicit C.

The exact source gaps are the normalization comparisons T1/T2 below: the
B_I-zero/packet normalization, the procession average/global weights, the
hull/possible-image/Ind1-3 identification, and the q-pilot 2l=82
normalization.  These are not arbitrary assumptions; they are the C9-specific
translation obligations.

## 1. Source side

From IUT III Corollary 3.12 (sources/IUT-III.txt lines 10152-10180):

- -|log(Theta)| in R union {+infinity} is the procession-normalized
  mono-analytic log-volume (average over j in F_l^x; Remark 3.1.1(ii)-(iv);
  Proposition 3.9(i)-(ii); Theorem 3.11(i)(a)) of the holomorphic hull
  (Remark 3.9.5(i)) of the union of possible images of a Theta-pilot object
  (Definition 3.8(i)), relative to the relevant Kummer isomorphisms
  (Theorem 3.11(ii)), in the multiradial representation of Theorem 3.11(i),
  subject to (Ind1),(Ind2),(Ind3).
- -|log(q)| in R is the same normalized log-volume of the image of a q-pilot
  object (Definition 3.8(i)), relative to the Kummer isomorphisms, in the
  multiradial representation, NOT subject to Ind1/2/3.
- Corollary 3.12 proves:
      -|log(Theta)| in R,
      -|log(Theta)| >= -|log(q)|,
      C_Theta >= -1 for -|log(Theta)| <= C_Theta |log(q)|.

A1-A3 exact schema:
A1 q-pilot input/representation: q-pilot at (1,0), fixed log-volume
   -|log(q)|, represented on 1,circ U^Q; not subject to Ind1-3.
A2 determinant/log-volume comparison: multiradial algorithm followed by hull
   and det^{tensor M}; comparable regions R_{<= -|log(Theta)|} and -|log(q)|.
A3 fixed q-pilot value: by SHE, the construction is under the fixed input
   q-pilot log-volume; hence -|log(q)| in R_{<= -|log(Theta)|}; inequality
   follows formally.

## 2. C9 side

C9 h_C and Q_C are defined in the C9 assembly as normalized log-volumes:

- h_C is the C9 normalized log-volume of the output target holomorphic hull
  H_C (finite bad contribution + arch h_inf; B_I-zero reference
  log-volume(B_I)=0; radial h=log r; global weights alpha_v=d_v/[F:Q]).
- Q_C is the C9 native q calibrated global log-volume of the q-pilot; in the
  uniform profile Q_p/log p = -b/e (e=41), so Q_p=-(b/41)log p.

The source quantities are different notation for the same normalized
log-volume functional:

    h_C = logvol_C9(H_C),    Q_C = logvol_C9(q-pilot).
    -|log(Theta)| = logvol_III(hull of possible images),
    -|log(q)| = logvol_III(q-pilot image).

T asserts that the two normalizations coincide on the same objects.

## 3. Conditional P6 theorem

Theorem 3.1 (conditional universal P6).  Assume:

(T) h_C = -|log(Theta)| and Q_C = -|log(q)| as identities of the normalized
    log-volume functionals on the C9 target hull and q-pilot;
(A1-A3) the IUT III Corollary 3.12 source schema for the fixed initial
    Theta-data/q-pilot input.

Then for every admissible fixed initial Theta-data/q-pilot input,
    Q_C = -|log(q)| <= -|log(Theta)| = h_C,
hence h_C >= Q_C, i.e. P6 true.

Proof.  Corollary 3.12 gives -|log(q)| <= -|log(Theta)|.  Apply T to both
sides.  QED.

No explicit complete C is used: the theorem is universal over the initial
Theta-data and the q-pilot input, and the source proof is a construction-
computation, not a construction of a C.

## 4. Exact normalization checks T1/T2

T is exact only if the following normalization comparisons hold.

### T1. h_C = -|log(Theta)|

T1a reference normalization:
- Source packet normalization: local holomorphic integral structure O has
  log-volume 0; nonarchimedean multiplication by p_v adds -log p_v;
  archimedean multiplication by e adds 1.
- C9 B_I-zero: log-volume(B_I)=0; radial h=log r; global weights
  alpha_v=d_v/[F:Q].
- For a complex archimedean place, O_{F_v} is the unit ball and B_I is the
  unit ball; both are normalized to zero and both use radial log.  Thus the
  archimedean local normalization matches.
- For nonarchimedean places, the C9 local log-volume must be the same
  p_v-adic Haar log-volume normalized on the integral structure O_{K_v}; the
  C9 finite height formulas are built with this normalization.  If the C9
  reference is a different integral structure or log-shell, an additive
  constant appears.

T1b procession average/global weights:
- Source uses the procession normalization: average of packet-normalized
  log-volumes over capsules, with normalized weights N_v and global degree
  identified with log-volume (Proposition 3.9(i)-(iii)).
- C9 uses alpha_v=d_v/[F:Q] and the C9 global assembly.
- T1 requires alpha_v = N_v and the C9 global sum/average to coincide with the
  source procession average, including the label average over j in F_l^x and
  the C6 alignment.  If only up to a constant c_h, then
      h_C = -|log(Theta)| + c_h,
  and the P6 conclusion is shifted.

T1c hull/possible-image/Ind:
- Source hull is the holomorphic hull of the union of possible images of the
  Theta-pilot, subject to Ind1/Ind2/Ind3.
- C9 H_C must be the same hull: same possible-image union (over j and v_Q),
  same Ind1/2/3, same B_I-zero normalization.  If C9 uses a target hull with
  a different possible-image set or resolves Ind3 differently, T fails by an
  additive/inequality constant.

### T2. Q_C = -|log(q)|

The source q-pilot log-volume is a normalized q_v zero-locus log-volume, not
raw log(q).  C9's native q value is
    Q_p/log p = -b/e = -b/41.
For the actual q_v=p_v^{2b} at the bad place, the q-pilot normalization uses
the 2l=82 root qhat (qhat^{82}=q_v; theta/Gaussian monoid normalization):
    -|log(q)| = -(1/82) log(q_v) = -(2b/82) log p_v
              = -(b/41) log p_v = Q_p.
Thus T2 is exact at the numerical level **provided** the C9/III q-pilot
normalization is the 2l=82 root normalization and q_v=p_v^{2b}.  If the source
q-pilot uses raw log q_v or a different root, T2 fails by a multiplicative
factor (a constant multiple of log p), which must be corrected before P6.

## 5. Exact obstruction if T is not exact

Let
    h_C = -|log(Theta)| + c_h,
    Q_C = -|log(q)| + c_q
for constants (or additive errors) c_h,c_q.  Corollary 3.12 gives
    -|log(q)| <= -|log(Theta)|
hence
    h_C - Q_C >= c_h - c_q.
Therefore:
- if c_h >= c_q, P6 holds for the corrected translation;
- if c_h < c_q, Corollary 3.12 alone leaves an additive gap c_q-c_h;
- a multiplicative mismatch d in h_C (h_C=d(-|logTheta|)) with d>0 preserves
  the inequality direction but changes the quantitative P6 margin; d<=0 or a
  different d for Q_C invalidates the direct comparison.

No such constants are computed in IUT III: the source proof defines the
normalized log-volume functionals abstractly.  C9 T1/T2 are therefore the
exact translation obligations.

## 6. What is established, what remains

ESTABLISHED:
- Source Cor3.12 schema A1-A3 and inequality -|log(q)|<=-|log(Theta)|.
- Conditional theorem: T + A1-A3 => P6, universally, without explicit C.
- Numerical q-pilot match for Q_p=-b/41 under the 2l=82 normalization.
- B_I-zero/arch normalization match at the unit-ball level.
- P6-true is universal; no explicit C is needed.

EXACT GAPS:
(T1a) nonarchimedean C9 local log-volume reference vs source integral
      structure/packet normalization;
(T1b) C9 alpha_v/C6 global assembly vs source procession average and normalized
      weights;
(T1c) C9 target hull/possible-image union/Ind1-3 vs source hull;
(T2) q-pilot 2l=82 normalization and q_v=p_v^{2b} vs C9 Q_p=-b/41; IUT III does
      not state an explicit numerical formula for |log q|;
(G1-G7) source-internal gaps of Cor3.12 (Theorem 3.11, determinant comparison,
      Ind1-3, compactness/finiteness, APT), as in the Cor3.12 extraction.

WITHDRAWN:
- treating h_C=-|log Theta| as an automatic consequence of notation;
- using raw log(q) instead of the normalized q-pilot log-volume;
- claiming P6 unconditionally without T1/T2;
- any mixed/E3 profile, any explicit C construction, any arch B_I lower bound.

## 7. Conclusion

If T holds exactly, P6 follows from Corollary 3.12 A1-A3 and is universal:
no explicit complete C is needed.  The source theorem supplies A1-A3; the
C9-specific content is exactly T1/T2.  The numerical q-pilot match
Q_p=-b/41 is consistent with the 2l=82 normalization; the remaining exact
checks are the B_I-zero/packet normalization, the procession/global weights,
the hull/possible-image/Ind1-3 identification, and the q-pilot normalization.
Without those checks T is only formal; with them T is an identity of normalized
log-volume functionals and P6 follows.

target_accepted=false; P6 open conditional on T+A1-A3.

## 8. Sources

- IUT III Corollary 3.12 and proof Steps (x)-(xi): sources/IUT-III.txt
  SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D,
  lines 10152-10180, 10520-10780.
- C9-P6TRUE-SCHEMA-20261025.md: A1-A3 + T schema; T pending.
- C9-COR312-QPILOT-20261025.md: A1-A3 q-pilot extraction; C9 translation
  separate.
- C9-COR312-THETAPILOT-20261025.md: definitions of Theta-pilot/hull/
  procession volume.
- C9-GLOBAL-ASSEMBLY-20261025.md: Q_p/log p=-b/41 and C9 global weights.
- C9-ARCHIMEDEAN-20261025.md: B_I-zero arch normalization; q-pilot zero locus.
