# C9 P6_norm master: proof assembly with named obligations

Task: task-388. Owner: multiradial. Date: 2026-10-25.
Natural-language proof assembly only. No Lean/Project edits; no mixed/E3; no
arbitrary data. Deliverable: this file only. target_accepted=false; P6 open.

## 0. Verdict

Strongest assembled P6_norm theorem:

    A1 (q-pilot input/representation)
    + A2 (determinant/log-volume comparison)
    + A3 (fixed q-pilot value/SHE membership)
    + T_norm (C9 normalized target translation)
    => for every admissible C:  Q_C^norm <= h_C^norm.

A1 is discharged as a source-input definition (q-pilot/BPS/0-column/LGP-link
are part of the Theorem3.11 situation); it is not a construction sorry.
A2, A3, and T_norm remain conditional source lemmas. Their exact gaps are
marked below as named natural-language sorries SORRY_A2, SORRY_A3,
SORRY_TNORM. No black-box source citation is used: each source theorem has an
exact statement and role.

P6_norm is NOT canonical P6. In the normalized convention
Q_C^norm=-|log q| and h_C^norm=-|log Theta|; Cor3.12 gives
Q_C^norm<=h_C^norm. The canonical C9Paper Q is Q_canon=d Q_norm with
d=[F_v:Q_p]=41 in the tame e=41 type. Therefore:

  - if both Q and h are normalized: P6_norm holds conditionally;
  - if Q is canonical QPaper and h is C6 normalized: Cor3.12 gives
    Q_canon<=41 h_C^norm, NOT Q_canon<=h_C^norm; factor-41 correction needed;
  - if both Q and h are canonical (h_canon=d h_norm): the inequality scales
    and canonical P6 follows, but this requires the canonical h convention,
    not the mixed C9Paper/C6 target.

No unconditional P6_norm or P6_canon is claimed.

## 1. Definitions and normalization

Let C be an admissible initial Theta-datum (IUT I Def3.1), F_mod=Q, l=41.

Normalized convention (N):
  Q_C^norm = -|log q| = procession-normalized log-volume of the q-pilot image,
             not subject to Ind1/Ind2/Ind3;
  h_C^norm = -|log Theta| = procession-normalized log-volume of the holomorphic
             hull of the union of possible images of the Theta-pilot,
             subject to Ind1/Ind2/Ind3.
  P6_norm: h_C^norm>=Q_C^norm.

Canonical convention (C):
  Q_C^canon = localSignedLog(qCandidate) = d * Q_C^norm,
  d=[F_v:Q_p]=41 in the tame totally ramified e=41 C9 type (E15).
  h_C^canon = d*h_C^norm only if the canonical hull-volume convention is used.
  P6_canon: h_C^canon>=Q_C^canon.

The C9Paper QPaper uses Q_canon; the C6/PaperP6 normalized target uses
h_C^norm. Mixing them gives the exact factor-41 mismatch, not an error of
Cor3.12.

## 2. A1: q-pilot input/representation (discharged by source input)

A1.1 q-pilot object: IUT III Def3.8(i), global realified Frobenioid object
determined by the q_v at v in V_bad, taken up to torsion. Its log-volume is
-|log q|; |log q|>0.

A1.2 Fixed/coric input prime-strip: Remark3.11.1(ii), the q-pilot
F^{value x mu}-prime-strip is fixed/rigidified by the 1-column arithmetic
holomorphic structure throughout the algorithm.

A1.3 1-column representation: Step(xi-a)-(xi-c); the q-pilot object at (1,0)
is represented on 1,circ U_Q via the 1-column log-Kummer correspondence and
the fixed ring structure (Remark3.12.2(iv): precise equalities in the
1-column, not merely upper bounds).

A1.4 IPL link: Remark3.11.1(iii); output data are linked to the fixed q-pilot
input by full poly-isomorphisms of F^{value x mu}-prime-strips induced by
algorithm operations; F^{value} is a full poly-isomorphism, F^{unit x mu} is
subject to Ind1/Ind2/Ind3.

A1 is source-input, not a sorry: it is the hypothesis "we are in the situation
of Theorem3.11" plus Def3.8/Remark3.11.1/Step(xi-a)-(xi-c). It does not
construct an E_546-specific BPS representative; P6_norm is universal over
admissible C and does not need one.

A1 residual exact gap: no canonical single q / numerical -|log q| is supplied
by A1 alone (q_v up to torsion; abstract poly-isomorphism class). This is a
source indeterminacy, not a construction gap; A2/A3 provide the comparison.

## 3. A2: determinant/log-volume comparison

A2.1 Hull to arithmetic vector bundle: Remark3.9.5(Ob1)-(Ob2); the holomorphic
hull is stabilized by O_K^times and defines local portions of a rank>1
arithmetic vector bundle over the 1-column local rings (Step xi-c).

A2.2 Determinant and O(-) adjustment: Remark3.9.5(Ob3-1); take suitable
positive tensor powers of the determinant of the direct summands, with the
inverse determinant of O(-) to match the Proposition3.9 normalization.
Ob3-2: det^otimes M, M positive and sufficiently divisible so localizations
are trivial. Ob3-3: arithmetic degree = log-volume up to standard
normalization.

A2.3 q-pilot comparison: Ob4; det^otimes M output is comparable to the M-th
tensor power of the q-pilot; extracting M-th roots and using normalized
weights gives comparability; tensor-power twists do not affect log-volume.

A2.4 Hull/Ind compatibility: Ob5-Ob9; upper-semi-compatibility, hull
approximants, log-Kummer/vertical-shift rectification, realified
semi-simplifications. The 1-column log-Kummer correspondence adjusts the
vertical shift between the unit portion of 1,0F^{value x mu}_Delta and the
log-shells of 1,circ U.

Conditional A2 theorem (strongest assembled):
  Assume D1-D5 as in C9-P6NORM-A2:
   (D1) bounded output hull defines finite-rank>1 arithmetic vector bundle E_H;
   (D2) det^otimes M with O(-)^{-1} exists and localizations trivial for M
        sufficiently divisible;
   (D3) deg(L_H)/M = mu_log(H) = -|log Theta|;
   (D4) q-pilot line bundle has arithmetic degree/log-volume -|log q|;
   (D5) tensor-power-twist and upper-semi-compatibility indeterminacies do
        not change normalized log-volumes.
  Then det^otimes M(E_H) tensor det^otimes M(O(-))^{-1} is a rank-1
  arithmetic line bundle comparable with L_q, with normalized degree
  -|log Theta|, and -|log q| lies in the same scale; R_{<=-|log Theta|} is
  well-defined and A3 supplies membership.

SORRY_A2 (named natural-language sorry):
  "The explicit O(-) determinant/degree identity, the integer M/weight
   normalization, the tensor-power-twist and upper-semi-compatibility
   invariance, the hull-approximant inequality, and the explicit vertical-shift
   adjustment are not written out in the source; A2 is conditional on D1-D5."
  Exact gaps G1-G7 of C9-P6NORM-A2:
   G1 O(-) adjustment ("routine details" left to reader);
   G2 explicit M/weights;
   G3 normalization factors;
   G4 tensor-power twists;
   G5 upper-semi-compatibility;
   G6 hull approximant inequality;
   G7 vertical-shift/log-Kummer rectification.
  A2 is not a black box: it is a conditional theorem from named source
  operations; SORRY_A2 is the exact unexpanded identity, not an arbitrary
  assumption.

## 4. A3: fixed q-pilot value/SHE membership

A3.1 Fixed input: the q-pilot F^{value x mu}-prime-strip is the coric/fixed
input; its pilot log-volume is -|log q|; |log q|>0 (Remark3.11.1(ii);
Theorem B/Cor3.12 statement).

A3.2 IPL: output data are linked to this fixed input by full poly-isomorphisms
of F^{value}-prime-strips (Remark3.11.1(iii); Step xi-b).

A3.3 SHE: the construction/output data are simultaneously expressed relative
to the domain arithmetic holomorphic structure (Theta-pilot) and the codomain
1-column structure. In the coric q-pilot case, SHE amounts to
expressibility under the fixed input pilot log-volume -|log q|
(Step xi-e; Remark3.11.1(iii)).

A3.4 Fixed value inclusion: Step xi-f asserts that the construction of
R_{<= -|log Theta|} constitutes a construction (perhaps up to indeterminacy
approximation) of the input pilot-object log-volume -|log q|. Hence
-|log q| in R_{<= -|log Theta|}; by definition of R,
-|log q| <= -|log Theta|; with |log q|>0, C_Theta>=-1.

SORRY_A3 (named natural-language sorry):
  "The source's 'perhaps only up to some sort of approximation' is converted
   into the actual set-membership -|log q| in R_{<=-|log Theta|}; the
   full-poly-isomorphism invariance of the pilot log-volume and the
   SHE-to-membership constitution relation are not separately proved."
  Exact gaps:
   G1 approximation semantics (indeterminacies/approximation vs actual
      membership);
   G2 invariance of the procession-normalized pilot log-volume under full
      poly-isomorphisms;
   G3 SHE-to-membership: define the constitution relation and derive
      membership, not merely an IPL link;
   G4 hull/log-volume finiteness/compactness/normalization (Prop3.9,
      Remark3.9.5) not expanded.
  A3 is not a black box: it quotes the exact SHE definition and Step
  (xi-e)/(xi-f); SORRY_A3 is the exact semantic/formal gap.

## 5. T_norm: C9 normalized target translation

T_norm statement:
  Under
   (H1) the C6 provenance/hull map from the source Theta-pilot possible-image
        set to the C6 tensor block/hull is the actual map;
   (H2) the procession average over j in F_l^× equals the C9 row average
        (the ±j pairing gives equality; no extra 1/2);
   (H3) the archimedean B_I-zero normalization is the source global
        log-volume/Prop3.9 readout;
  one has
   h_C^norm = -|log Theta|,
   Q_C^norm = -|log q|   if the normalized PaperP6 qLog is used.

Proof. C6 normalizedLogVolume is arithmeticTupleNormalizedLogVolume (1/D
degree normalization), not canonical localSignedLog. Under H1-H3 the source
normalized procession log-volume and the C6 normalized hull/arch readout agree.
The normalized q-pilot value is -|log q| by definition/source. QED.

SORRY_TNORM (named natural-language sorry):
  "The C6 provenance/hull map H1, the ±j procession-weight pairing H2, and the
   B_I-zero/source global readout identification H3 are source-alignment
   conditions, not independently proved identities."
  Exact gaps:
   T1 C6 actual identification/provenance map (H1);
   T2 procession label-pair/weight equality (H2);
   T3 B_I-zero arch/global log-volume normalization equality (H3).
  No explicit complete C is needed for T_norm, but the alignment is not
  optional: without H1-H3, h_C is only a C6 normalized volume, not
  automatically -|log Theta|.

Canonical factor:
  Q_C^canon = d*Q_C^norm, d=[F_v:Q_p]=41 in the tame e=41 type (E15).
  If h_C is the C6 normalized h_C^norm and Q is canonical QPaper:
     Q_canon <= d*h_C^norm = 41*h_C^norm, not Q_canon<=h_C^norm.
  If both Q and h are canonical (h_canon=d*h_norm), the normalized inequality
  scales to Q_canon<=h_canon; this requires the canonical h convention, not
  the mixed C9Paper/C6 target.
  SORRY_CANON: no theorem currently equates canonical QPaper Q and normalized
  C6 h without the factor; the factor 41 must be corrected or the normalized
  target chosen.

## 6. Main theorem: conditional P6_norm

Theorem P6_norm. Assume:

  A1 source input (discharged);
  A2 conditional determinant/log-volume theorem (SORRY_A2 gaps accepted);
  A3 conditional SHE/fixed-value lemma (SORRY_A3 gaps accepted);
  T_norm (SORRY_TNORM H1-H3 accepted).

Then for every admissible C, in the normalized convention (N),

    Q_C^norm <= h_C^norm.                                          (6.1)

Proof. Fix arbitrary admissible C. A1 supplies the fixed q-pilot input and
the 1,circ U output. A2 gives the comparable normalized log-volumes
-|log Theta| and -|log q| in the same scale. A3 gives
-|log q| in R_{<=-|log Theta|}. Hence -|log q|<=-|log Theta|. T_norm
identifies Q_C^norm=-|log q| and h_C^norm=-|log Theta|. Therefore
Q_C^norm<=h_C^norm. C arbitrary => universal P6_norm. QED.

No explicit complete C is constructed; the quantifier is universal over
admissible initial Theta-data. No mixed/E3.

## 7. What the named sorries mean exactly

SORRY_A1: DISCHARGED by source input definition (q-pilot/BPS/0-column/LGP-link
are part of the Theorem3.11 situation; no E_546-specific representative
needed). Residual: no canonical single q/numeric value; not required for the
universal inequality.

SORRY_A2: determinant/log-volume comparison. Exact statement: the normalized
arithmetic degree of det^otimes M(E_H) tensor det^otimes M(O(-))^{-1} equals
-|log Theta|, and the q-pilot normalized degree equals -|log q| in the same
normalization, with tensor-twist/upper-semi indeterminacies not changing the
comparison. Missing: G1-G7 above. This is a formal/identity gap, not an
arbitrary hypothesis.

SORRY_A3: SHE fixed-value inclusion. Exact statement:
-|log q| in R_{<=-|log Theta|}, and hence the inequality. Missing: G1-G3
above. This is a semantic/formalization gap, not an arbitrary hypothesis.

SORRY_TNORM: C9 target translation. Exact statement: h_C^norm=-|log Theta| and
Q_C^norm=-|log q| under H1-H3. Missing: C6 provenance/procession pairing/
B_I-zero arch alignments. This is a source-identification gap, not an
arbitrary choice.

SORRY_CANON: canonical P6 factor. Exact statement: Q_canon=d Q_norm=41 Q_norm;
Cor3.12 gives Q_canon<=41 h_C^norm, not Q_canon<=h_C^norm in the mixed target.
No theorem currently removes the factor 41; correction or normalized target is
required.

Upstream named source obligations (not sorries, but required input):
Theorem3.11(i)-(iii), Proposition3.9, Definition3.8, Remark3.9.5, IPL/SHE/APT/
HIS, IUT I/II/EtTh cyclotomic/Kummer inputs. Their proofs are outside Cor3.12.

## 8. P6_norm vs canonical P6: exact separation

| target | Q convention | h convention | Cor3.12 consequence |
|---|---|---|---|
| P6_norm | Q_norm=-|log q| | h_norm=-|log Theta| | Q_norm<=h_norm, conditional on A1-A3/T_norm |
| canonical both | Q_canon=d Q_norm=41Q_norm | h_canon=d h_norm=41h_norm | Q_canon<=h_canon (scales) |
| mixed C9Paper/C6 | Q_canon=41Q_norm | h_C=C6 normalized h_norm | Q_canon<=41 h_C, NOT Q_canon<=h_C |
| E15 equality case | d=1 | d=1 | normalized=canonical |

The current C9Paper QPaper/canonical target with normalized C6 h is the mixed
case; it is off by 41 unless corrected. P6_norm is the exact normalized
statement; canonical P6 needs either the canonical h convention or an explicit
conversion theorem.

## 9. Remaining gaps / next obligation

To eliminate the named sorries and obtain an unconditional P6_norm:

  1. SORRY_A2: display det^otimes M, O(-) inverse, M/weights, degree=log-volume
     identity, tensor-twist/upper-semi invariance, hull approximant, vertical
     shift (G1-G7).
  2. SORRY_A3: formalize approximation semantics, full-poly-isomorphism
     invariance of pilot log-volume, SHE-to-membership, hull/log-volume
     finiteness (G1-G4).
  3. SORRY_TNORM: prove C6 provenance/hull map H1, ±j procession pairing H2,
     B_I-zero arch/source readout H3.
  4. SORRY_CANON: if canonical P6 is required, prove canonical h convention or
     exact conversion; factor d=41 is exact.
  5. Upstream Theorem3.11/Prop3.9/Def3.8/Remark3.9.5/IPL/SHE/APT proofs.

None requires an explicit complete C; all are source-level construction/
normalization/formalization obligations. No mixed/E3; no arbitrary data.

## 10. Status and acceptance

Strongest assembled statement: P6_norm, universal, conditional on A1 (source
input), A2/A3/T_norm with named sorries above. A1 is discharged; A2/A3/T_norm
are not. P6_canon (mixed or canonical) is separate and factor-41 corrected.
No black box: every source theorem is named and every unexpanded step is marked
as a named sorry with exact gap.

No Lean/Project edits; no arbitrary data; no mixed/E3.
target_accepted=false; P6 open.

Only C9-P6NORM-MASTER-20261025.md written.
