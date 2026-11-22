# C9 CANONICAL A3 CLOSEOUT: exact membership from fitw

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 0. The problematic phrase

Step (xi-f), lines 10705-10711:

  'the construction of output data possibilities constitutes, in particular,
   a construction [perhaps only up to some sort of "approximation", as a
   result of various indeterminacies] of the pilot-object log-volume of the
   input data ..., namely, -|log(q)| in R.'

Then lines 10712-10715:

  'The inclusion -|log(q)| in R_{<= -|log(Theta)|}, hence also the inequality
   -|log(q)| <= -|log(Theta)| ... then follows formally.'

## 1. Resolution: approximation is up to indeterminacies, not a numerical epsilon

Remark 3.12.2(fitw), lines 10977-11022, states the logical relation:

  (q-itw) => (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets),

where '/indets.' means 'up to suitable indeterminacies (Ind1),(Ind2),(Ind3)'.
The second arrow is purely formal. The AND is a consequence of the AND in
(citw) via the subquotient operations of Remark 3.9.5(viii), whose compatibility
allows the conclusion. The source then says: 'Corollary 3.12 then follows,
essentially formally.'

Therefore the 'approximation' in xi-f is not an unknown numerical error term.
It is the indeterminacy quotient under which the multiradial output is formed.
The set R_{<= -|log(Theta)|} is the set of possible output log-volumes up to
those indeterminacies; exact membership means that the q-pilot log-volume is a
special case of the Theta-pilot output log-volume under this quotient.

## 2. A3 canonical statement and proof schema

A3: Q_can := -|log q| is in R_{<= h_can}, h_can := -|log Theta|.

Proof schema:
A3.1 (q-itw) the q-pilot intertwining is fixed/coric (A1).
A3.2 (q-itw) => (q-itw) AND (Theta-itw/indets): the multiradial algorithm
     constructs the Theta-intertwining simultaneously with/without invalidating
     the q-intertwining (Remark 3.11.1, Remark 3.12.2(eitw)).
A3.3 (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets): purely formal;
     the AND is obtained from the subquotient AND of (citw) via Remark 3.9.5(viii).
A3.4 Apply the log-volume to the Theta-intertwining up to indeterminacies;
     this is h_can and the possible output set R_{<= h_can}.
A3.5 The q-pilot log-volume Q_can is the special case of the Theta-pilot
     log-volume under the same quotient; hence Q_can in R_{<= h_can}.

Then Q_can <= h_can.

## 3. What is exact and what remains

Exact: the logical relation (q-itw)=>(q-itw)AND(Theta-itw/indets)=>(Theta-itw/indets)
is source-asserted and is not a numerical approximation.
Exact: the set R_{<=h_can} is defined by the log-volume readout of the Theta-pilot
output possibilities up to Ind1/2/3.

Residual formalization gap: the subquotient operations of Remark 3.9.5(viii)
and the 'AND' of (citw) are cited, not expanded. This is the only remaining
A3 formal gap; it is not an arbitrary epsilon and not a target/normalization
change.

## 4. Consequence

If the fitw logical relation and the subquotient AND are accepted as source
steps, A3 closes: Q_can in R_{<= h_can} exactly. No epsilon is introduced.

P6_can: A1 + A2 ratio + A3 fitw + T_can => Cor3.12 => P6_can.
P6: OPEN pending expansion of the fitw/subquotient step and T_can.
target_accepted=false.