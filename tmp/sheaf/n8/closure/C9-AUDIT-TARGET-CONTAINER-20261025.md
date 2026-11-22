# C9 target-container audit after Ind1 correction

Task: task-159 (C9 target-container audit after Ind1 correction)
Owner: multiradial
Date: 2026-10-25
Stage: SHEAF stage1 verification, natural language only. No Lean/Project edits.
Deliverable: this file only.

Status: audit complete. Task-148 and task-151 contain a substantial core of
valid arithmetic and correctly flagged open gaps, but several target-facing
claims depend on the withdrawn (11)-(14) target-container step, on TC-A to
TC-H, on the corrected symplectic donor, and/or on the conditional B=I branch.
Those claims are classified below. No new attack and no target closure is
claimed.

## 0. Audited files and versions

The audit uses the current bytes of the following files.

- tmp/sheaf/n8/closure/C9-IND1-GLOBAL-20261025.md
  SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8
  (the correction baseline; target-container conditions TC-A to TC-H).
- tmp/sheaf/n8/closure/C9-UNIFORM-HULL-20261025.md
  SHA256 99539B279B008CBEE367C14BC48AC11114460B0C0B706A71546FFDDC245A7D5B
  (task-148 deliverable; 255 current lines).
- tmp/sheaf/n8/closure/C9-GLOBAL-ASSEMBLY-20261025.md
  SHA256 6AB115790D8CDFD9E261985F7F209E4817C572AF6AAF4A48EB0EFDC2DE52CCF2
  (task-151 deliverable; matches the hash reported in the task).
- tmp/sheaf/n8/closure/C9-SYMPLECTIC-SOURCE-20261025.md
  SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70
  (task-147 correction of the symplectic donor).
- tmp/sheaf/n8/closure/C9-MODP-CERTIFICATE-20261025.md
  SHA256 E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95
  (task-155 deliverable; 250 current lines).

Version discrepancies:

- Task-148's final report says 232 lines, but the current file has 255 lines.
  The arithmetic values checked below agree with the current file; treat the
  task report line count as stale.
- Task-155's final report says line count 236, bytes 9487 and SHA256
  dad8163ff6ccbbe81faea5b8b341f8a9b2d3c664931dd9fe5b7a49fd73b29be8,
  but the current file has 250 lines and SHA256
  E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95.
  The current file already contains the corrected symplectic-source notice and
  the conditional B=O_K/B=I criterion. Audit the current bytes.

## 1. Correction baseline

C9-IND1-GLOBAL-20261025.md corrected the target-container audit:

- Equations (11)-(14) of C9-TAME-LOG-DOMAIN-20261025.md are not a target proof.
  They are conditional on target-container conditions TC-A to TC-H.
- Full Ind1 is the automorphism group of the procession
  Prc(n,circ D^dag_T), not finite label translation. Capsule permutations,
  D^dag-prime-strip isomorphisms, row/place, Theta/gluing, log branch, Ind2, and
  volume normalization are separate requirements.
- A ring isomorphism F does not by itself imply
  F(Hull(...)) subset H_C; either H_C must be Ind1-saturated or F must be an
  allowed target automorphism, plus the normalized-volume condition.

C9-SYMPLECTIC-SOURCE-20261025.md corrected the source donor:

- rho is not a homomorphism and no splitting is known;
- the actual donor is H = Phi^{-1}(Sp_{2g}(Z_p)), with rho the
  mapping-class/Dehn-twist set-theoretic source, not arbitrary boundary-word
  substitutions;
- the 2025 trace basis / 2026 symplectic basis alignment is an inferred
  convention, not a cross-paper theorem;
- the trace theorem is Tr_{K/K^{(d=1)}}, equal to Tr_{K/Q_p} only in the tame
  totally ramified case;
- J=m, the standard-lattice classification, orbit generation (7), and volume
  gain (8) are inferred consequences, not Kondo theorems.

C9-MODP-CERTIFICATE-20261025.md (task-155) gives the B-branch criterion:

- in the pi-power model, l = O_K/J = span(1) and Tr(pi^a)=0 for
  1<=a<=40; W0=ker Tr, dim 40; the trace line is l;
- under the natural 2025/2026 trace alignment, the line U of diag(1,Sp) is the
  trace line l, so v=0 and B=O_K;
- if the basis alignment fails, the actual W-coordinate v of l in F_p^40 is
  unknown; B=I occurs exactly when v is nonzero;
- therefore B=O_K is conditional on the alignment, and B=I is not actual from
  the current sources. Any claim that B=I is the selected source branch is
  invalid as written.

## 2. Classification rules

Each claim is classified by its strongest support:

A. Valid arithmetic: exact algebra/rational identities that do not depend on
   an unproved target container or on the corrected symplectic donor. Example:
   sums of s_j and evaluations of the displayed rational expressions.

B. Conditional source: depends on the corrected symplectic donor, the basis
   alignment, the low-ramification input, the local naturality interface, or a
   local Tate realization. It is not a published Kondo theorem and not an
   unconditional source construction.

C. Conditional target: depends on the withdrawn (11)-(14), on one of TC-A to
   TC-H, or on H_C being the same target container/row/Theta/log branch.
   It may be internally consistent but cannot be used as a proved target
   statement.

D. Invalid-as-written target claim: stated or used as an actual/proved target
   inequality, actual hull value, actual branch, or global h_C/Q_C conclusion
   without the source/target conditions above.

The corrected B=I branch is classified under C or D depending on the use:
conditional if explicitly kept as an unselected alternative, invalid if used
as actual or as a surplus in a global lower bound.

## 3. Task-148 ledger: uniform bad-profile hull bounds

Task-148 is C9-UNIFORM-HULL-20261025.md. Its own header says it only records
exact finite calculations from formulas (10), (14), (15), (17), and does not
bound the whole family C. That self-limitation is correct. The problem is the
classification of individual formulas and branch names.

### 3.1 Setup and local data

Items: e=41, m=20, p odd, p>e+1, pi^41=p u, J=m, b>0, 3|b, 41 not divide b;
s_j and t_j defined by b j^2 = s_j e + t_j.

Classification: B (conditional source).

Reason: the tame local field and pi-power model are source-level; J=m uses the
low-ramification input e<p-1; the symplectic donor is the corrected H, not the
withdrawn TAME Section 2 donor.

### 3.2 Equation (10-u): per-layer source-symplectic interior bound

Classification: B (conditional source), with the arithmetic part being A.

Reason: (10-u) is derived from the source-level formula (10), not from the
target hull H_C. It retains the tensor-order/integral-closure loss. It does not
require TC-A to TC-H. It does require the corrected symplectic donor and the
local naturality interface.

It cannot be used as a bound on H_C. Task-148's own Section 5 says (10-u) is a
tensor-order bound; that is consistent.

### 3.3 Equation (14-u): single all-bad field hull

Task-148 writes:

    nu(H_{C,j,p})/log p >= -s_j - 1/41.                        (14-u)

Classification: C (conditional target); invalid-as-written if called a proved
field-hull bound.

Reason: this is TAME (14), which is derived from the withdrawn target-container
step (11)-(13). It requires TC-A, TC-B, TC-C, TC-D, TC-E, and the fact that
H_{C,j,p} is the target hull of the all-bad branch. Task-148 Section 5 calls it
"the strongest per-layer field form"; that is a target claim, not a source
formula.

### 3.4 Equation (15-u), h_A, and "aligned full-Ind1 actual hull"

Task-148 writes:

    h_A(1,b) = -(1/20) sum_{j=1}^{20}(s_j + 1/41),             (15-u)

and in Section 5 calls (15-u) "the aligned full-Ind1 actual-output hull lower
bound" with "no tensor-order loss". It also says branch A is actual
(source-symplectic/aligned hull).

Classification: C (conditional target); D if "actual" is asserted.

Reason: TAME (15) depends on the target alignment (11)-(13). Task-148's own
Section 5 does not prove TC-A to TC-H; it imports the alignment from TAME.
Therefore h_A is a conditional target-hull value, not an actual H_C value.

This is the most important defect in task-148: its numerical tables are
internally correct but the label "actual/aligned hull" upgrades a conditional
target formula to a target proof.

### 3.5 Equation (17-u), h_B, and the B=O_K/I branch

Task-148 writes:

    h_B(1,b) = (1/20) sum_j [-s_j + j - (j+1)/41].             (17-u)

It labels branch A=O_K as actual and branch B=I as a possible larger subfamily
not proved. The second half is correct; the first half is too strong under
task-155.

Classification:
- h_B arithmetic: A (valid arithmetic) conditional on the branch formula.
- B=O_K: C (conditional on the 2025/2026 basis alignment); D if called actual
  without that alignment.
- B=I: C if explicitly conditional; D if used as actual or as a surplus in a
  global bound.

Reason: task-155's current certificate says natural trace alignment gives
v=0/B=O_K; if alignment fails, v is unknown and B=I is conditional. Neither
branch is unconditional from the corrected sources.

### 3.6 Exact numerical values

The following are valid arithmetic once the displayed formulas are accepted as
conditional expressions:

- sum_j s_j = 200 for b=3; h_A=-411/41; h_B=9/41; Q_p=-3/41;
  Q_p-h_A=408/41; Q_p-h_B=-12/41.
- sum_j s_j = 19100 for b=273; h_A=-39156/41; h_B=-38736/41;
  Q_p=-273/41; Q_p-h_A=38883/41; Q_p-h_B=38463/41.
- rho=1/2: b=3 h_{1/2}=-56311/10485760,
  h_direct=-120642551/10485760, Q=-3/82;
  b=1347 h_{1/2}=-51496081/10485760,
  h_direct=-172082321/10485760, Q=-1347/82.
- first direct-domain success b=1347; infinite tail via the TAME affine-period
  formula (which itself is conditional on the same local/target inputs).

Classification: A for the arithmetic evaluations of the displayed expressions;
C for any statement that these are actual H_C or global h_C values. The b=3
B=I surplus 9/41 is not actual under task-155's natural alignment; it is a
conditional alternative only.

### 3.7 "Branch A never reaches Q_p" and "only b=3 B=I could close"

These are valid arithmetic inequalities for the displayed formulas, but their
quantifiers are about the conditional branch formulas, not about the actual
source family. Classification: A/B for the inequality; C/D for any claim about
the real target.

### 3.8 p=12301 local Tate realization

Classification: B (conditional source).

Reason: the local Tate q realization is a source-level local model. It does not
construct a complete global C and does not prove the target hull. Task-148
correctly says this at the end of Section 6.

## 4. Task-151 ledger: global assembly

Task-151 is C9-GLOBAL-ASSEMBLY-20261025.md. It explicitly says it does not claim
G0 or a counterexample and that its "proved" statements mean natural-language
results in the frozen files. Those caveats are correct, but several target
claims still need correction.

### 4.1 Weights W1, templates W2/W3

- W1 (local weights alpha_v): A/paper-level valid.
- W2/W3 (global weighted sum and Q_C template): C/B. They are exact assembly
  templates, but no complete C with constructed weights and h_infinity is
  supplied.

### 4.2 T7/T8 and the "proved" source symplectic orbit

Task-151 Section 6 lists as proved:

- true Aut(G_K) symplectic orbit generation (T7) and hull increment (T8);
- finite transvection certificate SYM.

Classification: B (conditional source); D if listed as proved actual source
without the corrected donor.

Reason: T7/T8 are inferred consequences of the corrected H donor plus
basis alignment, low-ramification J=m, standard-lattice lemma, and local
naturality. They are not Kondo theorems. The original boundary-word
construction is withdrawn. The finite SYM certificate checks matrices, not the
source lift.

### 4.3 T9 tensor-order formula

Classification: B (conditional source), arithmetic A.

Reason: T9 is a local tensor-order computation, not a target hull claim. It
does not need TC-A to TC-H, but it does need the corrected source action. It is
not a global h_C bound.

### 4.4 T14 and T15: target hull lower bounds

Task-151 writes:

    nu(H_{C,j,p})/log p >= -s_j - 1/e,                         (T14)
    ell_j^aligned >= -rho^{j+1}(s_j+1/e),                      (T15a)
    h_p^aligned/log p >= -(1/m) sum ...                        (T15b)
    H_p^Sp/log p := -(1/m) sum (s_j+1/e).                      (T15c)

Classification: C (conditional target); D if called proved target or used as
an actual H_C lower bound.

Reason: these are exactly the withdrawn (11)-(14) target-container step. They
require TC-A to TC-H, especially TC-B (target saturation/F allowedness) and
TC-C (volume). Task-151 line 131 states "fixed gluing common terminal packet
map exists, full Ind1 orbit can be sent into the same target container
(GLUING (8)-(13)); this is why (T14) removes the tensor-order loss." That
statement is precisely the missing target-condition claim from
C9-IND1-GLOBAL-20261025.md; it is not proved by GLUING (8)-(13).

### 4.5 T16/G_p improvement

Classification: C/B; arithmetic A given T14.

The improvement formula G_p is algebraically correct once T14/T15 are granted.
But it compares a conditional target lower bound with the old source bound; it
does not establish an actual target improvement unless T14 is established.

### 4.6 T16b/T17a/T17b branch classification

Classification: C (conditional source/target); D for actual branch selection.

- T17a (A=O_K) is conditional on the basis alignment (task-155); it is not
  unconditional.
- T17b (B=I) is conditional if explicitly kept; it is invalid as actual.
- The statement "the actual source branch is B=..." is D in both cases until
  task-155's v=0 question is solved beyond the natural-alignment convention.

### 4.7 G1, G3, G4, G5, G6, G10

- G1:
    h_C >= sum alpha_p H_p^Sp log p + h_infinity(C).             (G1)
  Classification: C (conditional target); D if "proved global lower bound".
  It uses H_p^Sp, which uses T15/T14, plus the unconstructed global weights and
  h_infinity.

- G2/W3 Q_C:
  Conditional arithmetic template; native q readout from local data. Not a
  target proof; no complete C.

- G3/G4:
  D_p^Sp := Q_p - H_p^Sp log p and the identity for D_p^Sp are valid arithmetic
  given H_p^Sp, but H_p^Sp is conditional target. Classification A on the
  algebra; C on the interpretation.

- G5/G6/G10:
  Classification C; D if used to assert a global h_C<Q_C or G0 conclusion.
  G10 is correctly written as an inequality with the unknown
  h_infinity^actual(C); it cannot be used to decide the sign.

### 4.8 G7/G8/G9 numerical b=3, b=273

- The exact rational local values are A.
- G8's conditional "if h_infinity >= 0" and the local branch interpretation are
  C.
- The statement "b=3,B=O_K is the local deficit branch" is C/D under task-155:
  B=O_K is conditional on natural basis alignment, and B=I is not actual.
- The statement "b=3,B=I would give local surplus 9/41" is a conditional
  alternative (C), not an actual source branch (D if used as actual).

### 4.9 Archimedean gap and complete C gaps

These are correctly flagged and are valid open-gap statements:
- h_infinity^actual(C) not constructed;
- complete C bad set/weight construction not supplied;
- B=O_K/B=I decision not actual;
- no global G0 proof or complete counterexample.

Classification: valid gap acknowledgment (G), not target proof.

### 4.10 Task-151 Section 6 "proved" list

The list includes T7/T8/T14/T15 and GLUING (8)-(13) as proved. This
classification is invalid-as-written after correction:

- T7/T8 are conditional source (corrected H plus basis alignment/naturality).
- T14/T15 are conditional target (withdrawn target-container step).
- GLUING (8)-(13) supplies a common terminal packet transport for the chosen
  source family, but it does not prove the target-container saturation TC-B or
  the full Ind1 target containment required for T14.

The list must be split into A/B/C categories before it can be used by consumers.

## 5. Conditional B=I branch from task-155

Task-155 current file gives an exact criterion:

    l = span_Fp(1,v), v in F_p^40, in adapted U direct-sum W.
    v=0  => B=O_K, B=I not actual.
    v!=0 => B=I via Sp_40(F_p) transitivity.
    natural trace alignment => U=trace line=l => v=0 => B=O_K.

Therefore:

- B=I is not actual from the cited sources.
- B=O_K is conditional on the natural trace alignment (or on proving v=0).
- If the alignment fails, v is an exact finite unknown; no branch may be
  selected.

Effects:

- Task-148 b=3 h_B=9/41 and b=273 h_B=-38736/41 are conditional branch values.
  The b=3 surplus is not actual under natural alignment; using it as a source
  surplus is invalid-as-written.
- Task-151 b=3 B=I local surplus 9/41 is conditional/invalid-as-actual.
  Its own caveat "if B=I occurs" is acceptable only as a conditional branch;
  it cannot enter a global lower bound as an actual term.
- Task-151's "B=O_K local deficit" is conditional on basis alignment, not an
  unconditional actual branch.
- Task-155's current file itself is correctly conditional; the earlier task-155
  report hash mismatch means consumers must cite the current SHA E5056D...,
  not the stale dad8163... report hash.

## 6. Dependence ledger

The following table is the concise dependency map. A = valid arithmetic,
B = conditional source, C = conditional target, D = invalid-as-written target.

Claim or block                         | File | Depends on         | Class
---------------------------------------+------+--------------------+------
e=41, s_j/t_j tables, sums             | 148  | local data         | A/B
(10-u) per-layer tensor-order bound    | 148  | corrected H, local | B
(14-u) H_{C,j,p} bound                 | 148  | (11)-(14), TC-A/H  | C/D
(15-u), h_A "aligned actual"           | 148  | (11)-(14), TC-A..H | C/D
(17-u), h_B values                     | 148  | branch formula     | A
B=O_K "actual"                         | 148  | task-155 alignment | C/D
B=I "possible larger"                  | 148  | task-155 v unknown | C
b=3/b=273 rational comparisons          | 148  | formulas above     | A
rho=1/2 exact values                   | 148  | (15)/T14           | A/C
p=12301 Tate local realization          | 148  | source local data  | B
W1 weights                             | 151  | paper              | A
W2/W3 templates                        | 151  | complete C missing | B/C
T7/T8 "proved" orbit/hull gain         | 151  | corrected H, align | B/D
T9 tensor order                        | 151  | source local       | A/B
T14 target hull bound                  | 151  | (11)-(14), TC      | C/D
T15a/b/c aligned hull/H_p^Sp           | 151  | T14, TC            | C/D
T16/G_p improvement                    | 151  | T14                | A/C
T16b/T17a/T17b branches                | 151  | task-155 alignment | C/D
G1 global lower bound                  | 151  | T14/T15, h_infinity| C/D
G2/W3 Q_C template                     | 151  | complete C missing | B/C
G3/G4 D_p^Sp algebra                   | 151  | H_p^Sp            | A/C
G5/G6/G10 global comparison            | 151  | G1/T14/h_infinity  | C/D
G7/G8/G9 b=3,b=273 values              | 151  | branch conditional | A/C
archimedean/complete C gaps            | 151  | open               | G

## 7. Valid arithmetic inventory

The following are accepted as valid arithmetic conditional on the displayed
formulas, not as target claims:

- sum_j s_j = 200 at b=3; sum_j s_j = 19100 at b=273 for e=41.
- h_A(1,3)=-411/41, h_B(1,3)=9/41, Q_p(3)=-3/41;
  Q_p-h_A=408/41, Q_p-h_B=-12/41.
- h_A(1,273)=-39156/41, h_B(1,273)=-38736/41, Q_p(273)=-273/41;
  Q_p-h_A=38883/41, Q_p-h_B=38463/41.
- rho=1/2: b=3 h_{1/2}=-56311/10485760,
  h_direct=-120642551/10485760, Q=-3/82;
  b=1347 h_{1/2}=-51496081/10485760,
  h_direct=-172082321/10485760, Q=-1347/82.
- first direct success b=1347; the infinite tail uses the TAME affine-period
  formula (conditional on the same local/target inputs).
- exact rational bounds for branch A never reaching Q_p and for only b=3
  B=I potentially closing; these are arithmetic for the branch formulas.

No actual H_C, global h_C, or Q_C <= h_C conclusion follows from this
inventory.

## 8. Conditional source inventory

- corrected donor H=Phi^{-1}(Sp_{2g}(Z_p));
- rho mapping-class/Dehn-twist set map, not a homomorphism, no splitting;
- trace target Tr_{K/K^{(d=1)}}; equal to Tr_{K/Q_p} only in the tame totally
  ramified case;
- basis alignment between 2025 trace basis and 2026 symplectic basis: inferred,
  not paper theorem;
- H|U=id, H|W=Sp and the trace formula: conditional on the alignment;
- J=m and e<p-1 low-ramification input;
- standard-lattice classification and orbit generation (7);
- volume gain (8);
- local naturality between H's additive action and the C9 unit/tensor action;
- p=12301 local Tate realization.

These are not invalid; they are conditional. They must be cited as such.

## 9. Invalid-as-written target claims

The following claims, if retained as actual/proved, are invalid after
correction:

I1. Task-148: "(14-u) is the single all-bad field-tuple lower bound on the
target holomorphic hull H_{C,j,p}; strongest per-layer field form." It is a
conditional target formula.

I2. Task-148: "(15-u) is the aligned full-Ind1 actual-output hull lower bound
with no tensor-order loss; branch A is actual." It is conditional on TC-A to
TC-H.

I3. Task-148: "branch A=O_K is actual." B=O_K is conditional on task-155's
natural trace alignment; B=I is not actual.

I4. Task-148: numeric h_A/h_B as target hull values. They are arithmetic
expressions for conditional branch formulas, not actual H_C values.

I5. Task-151: T7/T8 listed as proved true Aut(G_K) orbit/hull gain. They are
conditional on the corrected H donor, basis alignment, low-ramification input,
standard-lattice lemma, and naturality.

I6. Task-151: T14/T15/H_p^Sp used as proved target hull lower bounds. They
depend on the withdrawn (11)-(14) and TC-A to TC-H.

I7. Task-151: G1, G6, G10 used as global target assembly statements. They are
conditional target formulas with missing h_infinity/complete C weights.

I8. Task-151: "full Ind1 orbit can be sent into the same target container
(GLUING (8)-(13)); this is why T14 removes tensor-order loss." This is exactly
the missing TC-B target-saturation condition, not a proved consequence of
GLUING (8)-(13).

I9. Any use of B=I as an actual source branch or as a global surplus. Under
task-155 natural alignment B=O_K and B=I is not actual; without alignment v is
unknown.

I10. Any use of the stale task-155 report hash dad8163... as the current
certificate. The current file hash is E5056D....

## 10. Repaired classification for task-148/151

Minimal correction pass, no new attack, no Lean edits:

For task-148 C9-UNIFORM-HULL-20261025.md:

1. Keep all exact rational arithmetic and s_j tables as A.
2. Relabel (10-u) as conditional source/tensor-order, not target hull.
3. Relabel (14-u) and (15-u) as conditional target formulas requiring TC-A to
   TC-H; remove "actual field hull" and "actual aligned hull" language.
4. Relabel h_A as conditional target under T14/T15; keep h_B as conditional
   branch formula.
5. Mark B=O_K as conditional on the 2025/2026 basis alignment; B=I as
   conditional/unselected, not actual.
6. Keep the b=3/b=273/rho=1/2 exact values, but label them arithmetic for
   conditional formulas, not H_C/global h_C.
7. Keep the local Tate p=12301 realization as conditional source; retain the
   "full C open" statement.

For task-151 C9-GLOBAL-ASSEMBLY-20261025.md:

1. Replace T7/T8 "proved" with conditional source under corrected H; cite
   C9-SYMPLECTIC-SOURCE, not the withdrawn TAME Section 2.
2. Replace T14/T15/H_p^Sp "proved target" with conditional target requiring
   TC-A to TC-H; cite C9-IND1-GLOBAL.
3. Replace line 131's "full Ind1 orbit can be sent into the same target
   container" with a named TC-B gap; GLUING (8)-(13) only gives the
   factor-permutation common packet map, not full target saturation.
4. Keep W1/W2/W3 as paper/template; mark global complete-C construction open.
5. Keep G3/G4 algebra as conditional arithmetic; mark G1/G6/G10 as conditional
   target and not G0.
6. Mark B=O_K/B=I as conditional on task-155; remove actual branch labels and
   actual B=I surplus from global lower bounds.
7. Correct the Section 6 "proved" list to A/B/C categories.
8. Update stale version references: task-148 current 255 lines; task-155 current
   SHA E5056D... and 250 lines.

## 11. Verdict

Task-148 and task-151 are not target proofs. They contain:

- a valid core of exact arithmetic and local source computations;
- a substantial set of conditional source statements that depend on the
  corrected symplectic donor and basis alignment;
- a target-facing layer that depends on the withdrawn (11)-(14) and TC-A to
  TC-H;
- an invalid-as-written set of "actual/proved target" claims and actual B=I
  uses.

The exact arithmetic values are useful and should be preserved. The target
claims must be downgraded to conditional target formulas until TC-A to TC-H
and the corrected source conditions are supplied. The B=I branch is not actual
under the natural trace alignment; without that alignment it remains an exact
finite unknown (v=0 vs v nonzero), not a selected surplus.

No global inequality h_C >= Q_C or G0 is established. No new attack and no
new target assumption is introduced. Lean/Project/kernel/comparator/independent
review not run; target_accepted=false.

## 12. Provenance summary

- Correction baseline: C9-IND1-GLOBAL-20261025.md
  SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8.
- Symplectic correction: C9-SYMPLECTIC-SOURCE-20261025.md
  SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70.
- Audited: task-148 C9-UNIFORM-HULL-20261025.md SHA256
  99539B279B008CBEE367C14BC48AC11114460B0C0B706A71546FFDDC245A7D5B;
  task-151 C9-GLOBAL-ASSEMBLY-20261025.md SHA256
  6AB115790D8CDFD9E261985F7F209E4817C572AF6AAF4A48EB0EFDC2DE52CCF2;
  task-155 C9-MODP-CERTIFICATE-20261025.md SHA256
  E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95.

End of C9-AUDIT-TARGET-CONTAINER-20261025.
