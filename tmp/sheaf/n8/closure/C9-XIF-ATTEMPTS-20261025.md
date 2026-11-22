# xi-f DIRECT NATURAL-LANGUAGE ATTEMPTS

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Goal: prove xi_f : Q ∈ R, with R independently defined.

Independent definition:
  R := { x in Real | exists a possible output datum D of the multiradial
        algorithm, modulo Ind1/Ind2/Ind3, such that logVol(D)=x }.
Q := -|log q| is the q-pilot log-volume.

This file tries several routes and records where each fails/succeeds.

## Attempt 1: exact local packet equality

Claim tried: for each v in V_bad, logVol(U_v) = Q_v = -(1/2l)log q_v.

Why it fails:
Theta ratios theta(U_j)/theta(U_0)=q_v^{-j^2/2} are theta VALUES, not the
log-volume of the local hull packet U_v. The log-volume is the Haar/procession
normalized measure of the hull; C9 TAME values show the local branch hulls are
H_A,H_B (e.g. b=3: H_A=-411/41, H_B=9/41), while Q=-3/41. They are different
numbers. The local output packet log-volume is not Q_v. REJECT.

Consequence: Strategy A (local exact equality) is not valid as stated.

## Attempt 2: IPL value-group pullback

Claim tried: IPL links output data to the fixed q-pilot prime-strip; the
F^value part is a full poly-isomorphism; log-volume is read from the value
group; hence some output has log-volume Q.

Why it fails:
If every output linked to the q-pilot input had log-volume Q, then the hull
log-volume h would equal Q for all C, contradicting Cor3.12's inequality
(h >= Q, not equality) and C9 TAME values. IPL links the output to the INPUT
q-pilot prime-strip; it does not identify the output hull log-volume with the
input value. The unit x mu portion and the hull/Ind operation change the
readout. REJECT.

## Attempt 3: determinant line bundle degree

Claim tried: L_H = det^tensor M(E_H) tensor det^tensor M(O(-))^{-1} is
isomorphic to L_q; hence deg(L_H)=deg(L_q)=Q; Q is an output log-volume.

Why it fails:
Cor3.12 only gives h >= Q, not h=Q; an isomorphism L_H≅L_q would force
equality, which is false for C9 TAME values. What the determinant comparison
gives is comparability of the objects, not equality of their log-volumes.
Also rank/O(-)/M/normalization are not displayed. REJECT as equality; only
comparison/inequality direction remains.

## Attempt 4: Ind orbit/closure

Claim tried: define R as the closure of {logVol(sigma D_0) | sigma in Ind}.
Source xi-e/f says the construction realizes Q 'up to indeterminacies';
so Q is a limit of Ind-transformed output log-volumes. If R is closed, Q in R.

Status: plausible but unproved.
- Need a base output D_0 and an explicit action of Ind on its log-volume.
- Need to show the set of values has Q as a limit (not just arbitrary).
- Need compactness/closedness of the output/hull space; previous review found
  the compactness/VQ finiteness unproved.
- Defining R as closure changes the source's R (which is a set of possible
  output values, not necessarily closed); this is a target-definition risk.

This is the only route that matches the source's approximation language, but
it requires substantial new proof (Ind action + compactness).

## Attempt 5: q-pilot as fixed point of the construction

Claim tried: the construction algorithm constructs its input q-pilot log-volume;
hence Q is a fixed point and lies in the image R.

Status: semantic, not a proof. 'Constitutes a construction' does not give a
map F with F(Q)=Q. APT says the algorithm is simultaneously valid in
domain/codomain, not that the input value is an output element. REJECT unless
a precise fixed-point theorem is supplied.

## Interim conclusion

None of Attempts 1-3 or 5 proves xi_f; they either confuse theta value with
log-volume, equality with inequality, or semantics with membership.
Attempt 4 is the only surviving direction: Ind-orbit/closure, but it needs
new proofs of the Ind action on log-volumes and compactness/closedness.

Therefore xi_f remains a named sorry. R is independently defined, but no
route currently establishes Q in R.

Next work: fill Attempt 4 with explicit Ind action formulas; or find a new
route not based on local arithmetic/equality.

P6: OPEN. No Lean.