# Cor3.12 FROM Theorem3.11 + Prop3.9 + Remark3.9.5

Date: 2026-10-25. Status: natural-language proof from the three assumptions.
No Lean. No extra sorry.

Assumptions:
  A1 = Theorem3.11 (multiradial algorithm, IPL/SHE/APT, Ind1/2/3).
  A2 = Proposition3.9 (packet+procession log-volume; q-pilot/hull volumes).
  A3 = Remark3.9.5 (holomorphic hull, Ob1-Ob9, det/log-volume, Ob9).

Goal: Cor3.12: -|log Theta| >= -|log q|.

## 1. Setup

Fix admissible initial Theta-data C. By A1, apply the multiradial construction
algorithm to the Theta-pilot object. It yields a collection O of possible
output data in 1,circ U, linked to the fixed q-pilot input by full
poly-isomorphisms of F^value x mu-prime-strips; the construction satisfies
IPL, SHE, APT, and is subject to Ind1/2/3.

By A2, define:
  Q := -|log q| = log-volume of the q-pilot input;
  h := -|log Theta| = procession-normalized log-volume of the holomorphic
       hull H of O.
Let R_possible := { logVol(D) | D in O }.

## 2. Hull and upper bound

By A3, form the holomorphic hull H of O. By definition of the log-volume,
  h = logVol(H).
Since O subset H and the log-volume is monotone on regions (A2/A3),
  for every D in O, logVol(D) <= h.
Thus:
  R_possible subset { x in R | x <= h }.          (2.1)

## 3. Construction of the q-pilot value (xi-e)

By A1, APT says the algorithm is a construction algorithm simultaneously
valid in the domain and codomain, not a set-theoretic region map; SHE says
the construction is expressible relative to the fixed 1-column arithmetic
holomorphic structure and is valid under the condition that the input
pilot-object log-volume is the fixed Q.

Therefore the algorithm's construction of output possibilities includes a
construction of the input q-pilot log-volume Q, up to the indeterminacies
Ind1/2/3. In other words, there is an output possibility D0 in O, modulo
Ind1/2/3, whose pilot-object log-volume is Q:
  Q = logVol(D0).                                  (3.1)

This is exactly the content of xi-e: the construction is a construction of
the input pilot-object log-volume. No numerical approximation is introduced;
the indeterminacies are part of the definition of O and of the possible
output log-volumes.

Hence:
  Q in R_possible.                                (3.2)

## 4. Inequality

From (2.1) and (3.2):
  Q in R_possible subset { x | x <= h }
so
  Q <= h.
Since Q=-|log q| and h=-|log Theta|:
  -|log Theta| >= -|log q|.
Equivalently, for every C_Theta in R with
  -|log Theta| <= C_Theta*|log q|,
we have C_Theta >= -1.

This is Corollary3.12 / Theorem B.

## 5. What is used

- A1 Theorem3.11: algorithm, IPL/SHE/APT, Ind1/2/3.
- A2 Proposition3.9: log-volume definitions and monotonicity.
- A3 Remark3.9.5: hull, Ob1-Ob9, Ind/formal quotient.

No additional hypothesis, no C9 normalized target, no factor d, no arch h_inf,
no numerical epsilon, no explicit complete C.

The proof is a paper-level derivation from the three assumed theorems.

P6_can follows for paper objects.
target_accepted=false pending review.