# xi-f / R DEFINITION AUDIT

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Question: does our independent R definition match IUT III?

## 0. Source definition

IUT III Step (xi-d), lines 10661-10666:

  R_{<= -|log(Theta)|}
    def = { lambda in R | lambda <= -|log(Theta)| } subset R;
  -|log(q)| in R.

So in the source, R is the real line and R_{<=h} is the HALF-LINE
  { lambda in R | lambda <= h }.
It is not defined as the set of achievable output log-volumes.

Step (xi-e), lines 10696-10704, then says the multiradial construction
algorithm, followed by hull and log-volume, 'yields a collection of possible
log-volumes of pilot-object output data R_{<= -|log(Theta)|} subset R'.

This is the substantive identification: the possible output log-volumes
are (or fill) the half-line R_{<=h}.

## 1. Our prior definition was different

We used:
  R_possible := { x in R | exists possible output datum D,
                              logVol(D)=x }.

That is the set of achievable output log-volumes, not the source half-line.
Using R_possible and then writing Q in R_possible is a different statement
from the source's Q in R_{<=h}.

## 2. Consequence: the tautology is in the source notation

If R_{<=h} is the half-line, then
  Q in R_{<=h}  <=>  Q <= h
is definitional. The source's 'inclusion follows formally' is exactly this
definitional equivalence. The real content is xi-e: the algorithm's possible
log-volumes are the half-line R_{<=h} (or at least contain Q and lie in it).

Our earlier R_possible was an attempt to make the content independent, but it
does not match the paper notation. We must not conflate:
  R_possible (achievable values)
  R_{<=h} (source half-line).

## 3. Corrected formulation

Define independently:
  R_possible := { x | exists possible output D, logVol(D)=x }.
Paper's R_{<=h} := { x | x<=h }.

The source's xi-e asserts (in effect) that the multiradial construction yields
possible output log-volumes equal to R_{<=h}; at minimum it must supply:
  (i) Q in R_possible;
  (ii) R_possible subset { x | x<=h }.
Then Q<=h.

(ii) is the hull/log-volume upper bound; (i) is xi-f. Neither is the paper's
definitional half-line statement alone.

## 4. Status

Our independent R definition did not match the paper; this is a concept
substitution and explains the tautology. The correct task is to relate
R_possible to the source half-line, not to define R_{<=h} as R_possible.

xi-f remains open. P6: OPEN. No Lean.