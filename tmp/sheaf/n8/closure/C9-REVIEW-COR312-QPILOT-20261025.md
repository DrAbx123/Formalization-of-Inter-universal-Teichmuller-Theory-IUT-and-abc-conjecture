# C9 review: q-pilot / SHE / IPL in the unconditional Cor3.12 NL proof

Task: task-419. Reviewer: multiradial. Date: 2026-10-25.
Review only; no rewrite, no Lean/Project edits, no mixed/E3. Deliverable:
this file only. target_accepted=false; P6 open.

## 0. Reviewed text

C9-COR312-UNCONDITIONAL-NL-20261025.md, Section4 "Fixed q-pilot value and SHE
(xi-e)" lines 93-113, and the subsequent use in Section5/6 lines 115-170.
Source: IUT-III.txt SHA256
822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

Review question: is the fixed q-pilot value used correctly, and is there any
normalized surrogate? Accept/reject per step.

## 1. Verdict

PARTIAL ACCEPT / PARTIAL REJECT.

  - ACCEPT the q-pilot fixed-value/input statements: the q-pilot log-volume is
    -|log q|, fixed and not subject to (Ind1),(Ind2),(Ind3); IPL links the
    output data to this fixed input by full poly-isomorphisms of
    F^⊩▶×mu-prime-strips; SHE is a source property of the construction
    relative to the 1-column arithmetic holomorphic structure.
  - REJECT the step that treats the fixed q-pilot VALUE as if it were one of
    the possible OUTPUT log-volumes. IPL links prime-strips/categories; it does
    not assert that the q-pilot log-volume is an element of R_{<=-|logTheta|}.
    The q-pilot object is at (1,0) and is not subject to Ind1-3; R is the set
    of output log-volumes subject to Ind1-3. The identification of the fixed
    input value with a possible output value is the xi-f semantic gap, not a
    consequence of IPL/SHE.
  - REJECT the resulting "unconditional" inclusion/inequality: the proof's
    statement "the closed loop exhibits the q-pilot object as one of the
    possible output data" is stronger than the source text. The source says
    the construction constitutes a construction of the input pilot log-volume
    "perhaps only up to some sort of approximation"; it does not state the
    exact membership.
  - No normalized surrogate is detected in Section4: it uses the source
    packet q-pilot log-volume -|log q|, not Q_norm=Q_can/d. No factor 41/82 is
    introduced there. This does not repair the xi-f membership gap.

Therefore Section4's q-pilot/SHE/IPL data-level statements are faithful, but
its use of the fixed q-pilot value as an output value is not justified.
Cor3.12 remains conditional on the exact xi-f membership; the unconditional
claim is rejected.

## 2. Step-by-step accept/reject

### Step 4.1 (lines 95-96): q-pilot input fixed, -|log q|, not subject to Ind1-3
VERDICT: ACCEPT.
Source: Cor3.12 statement lines 10166-10176: -|log q| is the
procession-normalized mono-analytic log-volume of the q-pilot image, "which we
do not regard as subject to the indeterminacies (Ind1),(Ind2),(Ind3)"; Step
xi-a/b q-pilot at (1,0); Remark3.11.1(ii) fixed/coric input. The q-pilot is an
input object, not a family of possible output images.

### Step 4.2 (lines 96-97): IPL links output to fixed input by full
poly-isomorphisms of F^⊩▶×mu-prime-strips
VERDICT: ACCEPT (data-level).
Source: Remark3.11.1(iii) IPL lines 9524-9539; Step xi-b lines 10605-10620.
The F^value part is a full poly-isomorphism; the F^unit×mu part is subject to
(Ind1)-(Ind3). This is a link of prime-strips/constructions, not an equality of
log-volumes. The section correctly notes the split.

### Step 4.3 (lines 99-109): SHE / 1-column expressibility
VERDICT: ACCEPT AS SOURCE PROSE; CONDITIONAL AS FORMAL STATEMENT.
Source: Remark3.11.1(iii) SHE lines 9562-9600; Step xi-e lines 10682-10704.
SHE is "simultaneous holomorphic expressibility" of the construction relative
to the domain and codomain arithmetic holomorphic structures. The equivalence
"expressibility ... amounts precisely to ... fixed pilot-object log-volume" is
the source's interpretive formulation, not a separately stated theorem. It is
acceptable as a source reading, but it is not a formal set-membership proof.

### Step 4.4 (lines 111-113): q-pilot value linked to possible output data
VERDICT: REJECT AS STATED.
What follows from IPL is a link of the output F^⊩▶×mu-prime-strips to the
input q-pilot prime-strip. The q-pilot log-volume is the value of the input
object (not subject to Ind1-3), while the possible output data are in
1,circ U subject to Ind1-3. A poly-isomorphism link between the constructions
does not imply that the input value is an element of the set of output
log-volumes. The phrase "the q-pilot value is linked ... to the possible output
data" conflates object-link with value-membership. This is the first exact
overreach.

### Step 4.5 (Section5, lines 146-158): closed loop exhibits q-pilot object as
one of the possible output data
VERDICT: REJECT.
The source Step xi-f says the construction of R_{<=-|logTheta|} is subject to
the condition that it constitutes a construction (perhaps only up to an
approximation due to indeterminacies) of the pilot-object log-volume of the
input data. That is weaker than "the q-pilot object is one of the possible
output images." The NL proof upgrades:
  construction computes/approximates the input pilot value
to:
  input pilot value is an exact element of R_{<=-|logTheta|}.
That upgrade is the xi-f gap already identified as SORRY_A3/M1; IPL/SHE do not
supply it. The source's "perhaps only up to some sort of approximation" is not
a proof of exact membership.

### Step 4.6 (Section6, lines 160-168): final inclusion and inequality
VERDICT: CONDITIONAL; UNCONDITIONAL CLAIM REJECTED.
If Step 4.5 is granted (exact membership), then -|log q|<=-|log Theta| and
C_Theta>=-1 follow. But Step 4.5 is not established by Section4; it is the
xi-f source gap. Therefore the final inclusion is conditional on the missing
exact membership, and the Section8 "unconditional over admissible initial
Theta-data" conclusion is rejected as a proof claim.

## 3. Normalized surrogate check

Section4 uses the source packet value -|log q|, not Q_C^norm=Q_can/d.
No factor 41, no factor 82, no C9 normalized surrogate is introduced in the
reviewed section. This part is correct.

However, avoiding a normalized surrogate does not validate value-membership.
The issue is object/value level:
  - q-pilot value: input value, not subject to Ind1-3;
  - possible output value set R: outputs of the Theta-pilot algorithm,
    subject to Ind1-3.
The equality of the source packet q-log with a possible output log-volume is
the nontrivial xi-f assertion, not a definition.

## 4. Exact reasons and source limits

Accepted source facts:
  - q-pilot is fixed/coric and not subject to Ind1-3 (Cor3.12 statement,
    lines 10166-10176; Remark3.11.1(ii));
  - IPL is full poly-isomorphism of F^⊩▶×mu-prime-strips with F^unit×mu
    indeterminacies (Remark3.11.1(iii); Step xi-b);
  - SHE is expressibility relative to the 1-column arithmetic holomorphic
    structure (Remark3.11.1(iii); Step xi-e);
  - the closed loop sQ1-sQ4 and Ob9-1 compatibility are source constructions
    for comparability of coarse invariants (Section5; Remarks3.9.5(viii),(ix),
    3.10.2).

Rejected inference:
  - IPL/SHE do not imply q-pilot value ∈ R_{<=-|logTheta|}. The step
    "closed loop exhibits q-pilot object as one of the possible output data"
    is not in the quoted source; the source only asserts a construction of the
    input pilot log-volume up to indeterminacy/approximation.
  - The exact membership is the xi-f gap. Without it, Section6's inequality is
    conditional, not unconditional.

No arbitrary data, mixed/E3, or normalized surrogate is used in this review.
No Lean/Project edits.

## 5. Verdict summary table

| step | statement | verdict |
|---|---|---|
| 4.1 | q-pilot fixed, -|logq|, not subject to Ind1-3 | ACCEPT source |
| 4.2 | IPL links output to fixed input by full polyiso | ACCEPT data-level |
| 4.3 | SHE = 1-column expressibility | ACCEPT source prose; not formal membership |
| 4.4 | q-pilot value linked to possible output data | REJECT as stated; object-link ≠ value-membership |
| 4.5 | closed loop exhibits q-pilot as possible output | REJECT; stronger than source xi-f |
| 4.6 | final inclusion/inequality unconditional | REJECT unconditional; conditional on xi-f membership |
| 4.7 | no normalized surrogate in Section4 | ACCEPT; factor not the issue here |

## 6. Conclusion

The q-pilot/SHE/IPL portion of the unconditional proof is mostly faithful at
the data/construction level: the q-pilot is correctly fixed and not subject to
Ind1-3; IPL and SHE are correctly cited; no normalized surrogate appears.
However, the proof misuses the fixed q-pilot VALUE as if it were an exact
possible output log-volume. IPL/SHE establish a link of prime-strips and a
construction up to indeterminacy, not the exact membership
-|log q| ∈ R_{<=-|log Theta|}. The source's "perhaps up to approximation"
wording is a gap, not an exact membership proof. Therefore the unconditional
claim is REJECTED; Cor3.12 remains conditional on the xi-f exact membership/
signed-error step. No rewrite of the reviewed file; no Lean/Project edits;
target_accepted=false.

## 7. Acceptance

Only C9-REVIEW-COR312-QPILOT-20261025.md written. Review only; no rewrite; no
Lean/Project/target edits; no mixed/E3; target_accepted=false.
