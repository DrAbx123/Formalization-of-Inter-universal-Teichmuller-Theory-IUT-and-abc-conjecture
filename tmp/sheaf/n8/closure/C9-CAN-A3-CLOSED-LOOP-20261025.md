# C9 CANONICAL A3 — CLOSED-LOOP / SUBQUOTIENT EXPANSION

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 0. Goal

A3 for paper P6_can:
  Q_can = -|log q| in R_{<=h_can},  h_can = -|log Theta|.

Surviving source route: closed loop of F^⊩▶×μ-prime-strip poly-isomorphisms
through (sQ1),(sQ2),(sQ3),(sQ4), with log-Kummer compatibility, yielding a
prime-strip simultaneously equipped with the Theta-intertwining (up to
Ind1/2/3) and the q-intertwining. Then apply log-volume.

## 1. The chain (Remark3.9.5(viii),(ix); lines 8383-8431)

The closed loop:

  q-pilot object in the codomain of the Theta x mu LGP-link
    -> Theta x mu LGP-link to the domain
    -> poly-isomorphisms of F^⊩▶×μ-prime-strips induced by (sQ1),(sQ2)
       (IPL; Remark3.10.2)
    -> (sQ3),(sQ4), compatible with the log-Kummer correspondence
       (cQ3),(cQ4)
    -> back to the q-pilot object.

Source: lines 8383-8405.

Only if this loop is closed can one complete the computation of the
projection of the Theta-intertwining onto the q-intertwining, i.e., complete
the Theta-intertwining structure up to suitable indeterminacies on a
prime-strip constrained to be subject to the q-intertwining. Skipping (sQ3)
or (sQ4) breaks the loop and yields no nontrivial conclusion (lines 8406-8431).

## 2. The AND

(citw), lines 10913-10943, says: the two arithmetic holomorphic structures in
domain/codomain of the LGP-link are distinguished, so both the Theta-
intertwining and the q-intertwining are simultaneously valid:

  (q-intertwining holds) AND (Theta-intertwining holds).

Remark3.12.2(fitw), lines 10977-10998, weakens to indeterminacies:

  (q-itw) => (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets).

The second arrow is purely formal. The AND of the middle display is the image
of the AND of (citw) via the subquotient operations of Remark3.9.5(viii).
The closed loop above is precisely the construction that realizes this AND:
a prime-strip simultaneously equipped with both intertwinings (lines 8417-8424).

## 3. Applying log-volume

The Theta-intertwining up to Ind1/2/3, followed by the holomorphic hull and
the procession-normalized log-volume, gives h_can = -|log Theta| and the set
R_{<=h_can} of possible output log-volumes (xi-d, xi-e).

The q-intertwining is the q-pilot input; its log-volume is Q_can = -|log q|.

Since the closed-loop prime-strip is simultaneously equipped with both
intertwinings, the q-pilot log-volume is the projection/special case of the
Theta-pilot output log-volume under the same indeterminacy quotient. Hence

  Q_can in R_{<=h_can}.

By definition of R_{<=h_can}, this is Q_can <= h_can.

## 4. Exact remaining gaps

CL1. The 'formal quotient indeterminacies' of (cQ3),(cQ4) and (Ob9-1) are
     described but not expanded as exact quotient operations.
CL2. The compatibility of (sQ3),(sQ4) with the log-Kummer correspondence
     is source-asserted (cQ3),(cQ4), not proved line by line.
CL3. The identification of the subquotient AND with the AND of (citw) is
     source-asserted via Remark3.9.5(viii); it is not a set-theoretic map.

These are the exact residual A3 gaps. They are not numerical epsilon, not
normalization factors, and not target changes.

## 5. Consequence

If CL1-CL3 are accepted/expanded, A3 closes exactly: Q_can in R_{<=h_can}.
Then P6_can follows from Cor3.12, with A1 source-input and A2 ratio identity.

P6_can: conditional on CL1-CL3 and T_can.
P6: OPEN. target_accepted=false.