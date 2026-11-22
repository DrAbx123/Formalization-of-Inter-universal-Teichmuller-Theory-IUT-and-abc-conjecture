# C9 P6_can REVIEW SUMMARY — NATURAL PROOF NOT ACCEPTED

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Inputs: C9-P6-CAN-NATURAL-PROOF, V2, self-audit, 8 independent reviews.

## 0. Bottom line

The natural-language proof is NOT accepted as a complete proof of P6_can.
It is accepted only as a conditional schema. The main obstruction is A3:
the claimed derivation of Q_can in R_{<=h_can} is exactly the content of
Cor3.12 xi-e/xi-f, so claiming it as a consequence of CL1-CL3 is circular
unless xi-f is itself accepted as the source theorem.

## 1. A1

ACCEPTED at object/class level with corrections:
- full-poly class is the codomain q-pilot F^value x mu class, not the whole LGP-link;
- q_v is up to torsion; Q_pilot object is canonical; attach torsion to generators;
- Q_can=-|log q| is the log-volume of the q-pilot image in the multiradial
  representation (Theorem B), not merely abstract Q_pilot;
- numerical Q_can=-(b/41)logp is a C9/TAME normalization hypothesis, not an
  IUT III displayed theorem;
- q-pilot is at (1,0), not on the 0-column; 0-column carries Theta-pilot/
  vertically coric data and LGP-link to 1-column.
Status: A1 acceptable with these corrections.

## 2. A2

V1 was REJECTED: E_H/det^tensor M/O(-)/M/rank normalization not displayed.
V2 observation: Ob3-3 says the determinant intermediate step may be OMITTED
when only log-volumes are being computed. Therefore the P6 inequality does
not need the determinant identity; h_can and Q_can are defined as log-volumes.
Status: A2 determinant objection is moot for P6_can if we use Ob3-3.
Caveat: this is a definitional reduction, not a proof of the determinant
identity; reviewers of V1 did not review V2.

## 3. A3

REJECTED as an independent proof.
- Transport review: CL2.3 non-sequitur: cQ3/cQ4 give compatibility of
  individual sQ3/sQ4, not the composite closed loop; the closed loop is a
  separate source assertion (Remark3.9.5(ix)).
- CL3.3 false: source (iQ5) says sQ5 is INCOMPATIBLE with F^units x mu data;
  it is the final coarse quotient after the closed loop, not compatible CL1/CL2.
- CL3.5 circular: Q_can in R_{<=h_can} is exactly Cor3.12 xi-e/xi-f, not
  derived from CL1-CL3.
- Source xi-f says 'perhaps only up to some sort of approximation'; exact
  membership is the source's formal conclusion, not an independently computed
  set-theoretic membership.
Status: A3 is a source-conditional restatement, not an expanded derivation.

## 4. T_can

Definitional only if the C9 target objects are DEFINED as the paper objects.
For an independently defined C9Paper q-scalar/native q, the identity
C9QPilot=IIIQPilot is a gap (C2 rejected by multiradial review).
The normalized Lean target is a different finite target; it is not paper P6_can.

## 5. Consequence

P6_can is NOT proved by the natural-language file.
The only remaining routes:
(a) accept Cor3.12 xi-e/xi-f as the source theorem (then P6_can follows,
    conditional on A1/T_can); this is source-theorem acceptance, not a
    black-box-free derivation;
(b) prove A3 exact membership independently (open; source allows approximation);
(c) find a different proof of P6_can not via A3.

P6: OPEN. target_accepted=false. No Lean.