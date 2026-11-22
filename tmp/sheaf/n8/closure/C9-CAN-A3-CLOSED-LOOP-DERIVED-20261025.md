# C9 A3 — CLOSED LOOP AND xi-f MEMBERSHIP DERIVED

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 0. Goal

Derive, not merely cite:
  (i) the closed loop through sQ1-sQ4;
  (ii) Q_can in R_{<=h_can} from the closed loop.

## 1. What a full poly-isomorphism class means

By Def2.4(iii)/Def3.8(ii), an F^⊩▶×mu-prime-strip is determined by its
F^value and F^unit×mu data; a full poly-isomorphism is an isomorphism of
these data, with no chosen representative. Two such prime-strips with the
same F^value×mu data are therefore full-poly-isomorphic.

This is the key point: the F^value×mu data determine the full-poly class.

## 2. Closed loop derived

Let S_q be the q-pilot object of the codomain F^⊩▶×mu-prime-strip at (1,0).

Step 1. The LGP-link is a full poly-isomorphism of F^⊩▶×mu-prime-strips
  from the domain (Theta-pilot side) to the codomain (q-pilot side)
  (Def3.8(ii)). Apply it to the Theta-pilot object.

Step 2. sQ1 (Kummer-detachment) and sQ2 (Galois evaluation) are the
  poly-isomorphisms of F^⊩▶×mu-prime-strips of Remark3.10.2; applying them
  to the LGP-link output gives a chain of poly-isomorphisms from the
  Theta-pilot side to the output data in 1,circ U.

Step 3. sQ3 (det^tensor M/hull/⊼) and sQ4 (log-Kummer vertical shift)
  are compatible with the F^⊣×mu-prime-strip data by cQ3/cQ4 (derived in
  C9-CAN-A3-COMPATIBILITY-DERIVATION): they produce the same G_v and O^×mu
  actions and the same value-group data as the q-pilot input. In particular,
  the resulting F^value×mu data are exactly those of S_q, up to the formal
  indeterminacies of Ob9-1 (tensor-twist, ⊼, log-link iterates), which by
  Ob9-1 have no effect on comparability.

Step 4. By Section 1, two F^⊩▶×mu-prime-strips with the same F^value×mu data
  are full-poly-isomorphic. Therefore the composite of Steps 1-3 is a full
  poly-isomorphism from S_q to an object with the same F^value×mu data as S_q,
  i.e. to S_q itself up to full poly-isomorphism. This is the closed loop.

Thus the closed loop is not an extra axiom: it is the composition of the
LGP-link, the Remark3.10.2 poly-isomorphisms, and the cQ3/cQ4-compatible
sQ3/sQ4 operations, using the fact that F^value×mu data determine the
full-poly class.

## 3. xi-f membership derived

Define R_poss to be the set of log-volumes of possible output data in
1,circ U, up to the indeterminacies Ind1/Ind2/Ind3; R_{<=h_can} is its
downward-closed hull.

By Section 2, the closed loop exhibits the q-pilot object S_q as one of the
possible output data of the multiradial algorithm (up to the same formal
indeterminacies). Therefore its log-volume Q_can is one of the possible
output log-volumes:
  Q_can in R_poss.
Since R_poss is contained in R_{<=h_can} by the hull/log-volume monotonicity
of xi-d/xi-e, we obtain
  Q_can in R_{<=h_can}.
By the definition of R_{<=h_can}, this is Q_can <= h_can.

The 'perhaps approximation' parenthetical in xi-f refers to the formal
indeterminacies (Ob9-1), which are already quotiented out in R_poss. It is
not an additional numerical error: the q-pilot volume is the same fixed
Q_can, and the set R_poss is defined up to those indeterminacies.

## 4. Residual assumptions (explicit)

CL-A. F^value×mu data determine the full-poly class (Section 1; Def2.4/Def3.8).
CL-B. sQ1/sQ2 poly-isomorphisms of Remark3.10.2 compose with LGP-link.
CL-C. sQ3/sQ4 produce the same F^value×mu data as S_q (cQ3/cQ4 derivation).
CL-D. Ob9-1 formal indeterminacies have no effect on comparability; R_poss is
      defined up to them.

These are the exact assumptions used. They are source-structural, not
numerical epsilon and not target/normalization changes.

## 5. Consequence

If CL-A..CL-D hold, A3 closes: Q_can in R_{<=h_can}.
Then P6_can follows from Cor3.12, with A1 source-input and A2 definitional
(Ob3-3: determinant step omitted for log-volume).

P6_can: conditional on CL-A..CL-D.
P6: OPEN. target_accepted=false.