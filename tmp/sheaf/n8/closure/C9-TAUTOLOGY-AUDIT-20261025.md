# C9 TAUTOLOGY AUDIT — xi-f / Cor3.12 / P6

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Purpose: check whether the current 'proof' is a tautology/subsumpion.

## 0. Verdict

YES, the final implication is tautological once xi-f membership is assumed.
The real content is exactly xi-f (q-pilot is a possible output log-volume),
which we have only as a named sorry/source assertion.

## 1. The tautology

Define
  R_{<=h} := { x in R | x <= h }.
Then the implication
  q in R_{<=h}  =>  q <= h
is true by the definition of R_{<=h}. It is not an inequality theorem.

In Lean this is:
  StepXIContract has fields q_le_target and target_le_theta;
  Cor312Conclusion is q <= theta;
  cor312_of_constructed_stepXI is le_trans q_le_target target_le_theta.
That theorem is pure transitivity, not a proof of the source inequality.

Our C9P6CanFormal.lean has the same shape:
  Rposs_upper : forall x in Rposs, x <= hcan
  Sq_possible : Qcan in Rposs
  p6_can := Rposs_upper Qcan Sq_possible.
Also tautological wrapper.

## 2. Where the real content is

The only non-tautological statement is xi-f:
  Qcan in R,
i.e. the q-pilot log-volume is one of the possible output log-volumes of
the multiradial algorithm.

Source says: construction of output possibilities constitutes a construction
of the input q-pilot log-volume 'perhaps only up to approximation'; then the
inclusion follows formally. That formal inclusion is the source's theorem;
if we only quote it, xi-f is a named sorry.

## 3. Circularity risks

- Closed loop/cQ3/cQ4 produce simultaneous intertwinings, not q-pilot
  membership; using them to prove q in R is circular.
- 'Constitutes a construction of q' is semantic; equating it with exact
  membership is the very step that must be proved.
- A2 determinant/Ob3-3 'suitable normalization' can hide the q/h equality;
  not an independent numerical comparison.

## 4. What would be non-tautological

N1. Construct an explicit output object U whose logVol is Qcan (or prove
    local exact equality whose sum is Qcan).
N2. Prove exact deg(L_H)=deg(L_q) in a fixed normalization and identify both
    with h/Q.
N3. Prove R is closed and Qcan is a limit of output values (with compactness
    and continuity), so membership is not definitional.

Any of N1-N3 would be real mathematical content. Current attempts A/B/C did
not establish them; reviews rejected the missing pieces.

## 5. Consequence

The Stage1 contract is honest as a named-sorry boundary, but it is NOT a
reduction of the theorem to simpler facts: it names the content xi-f.
Cor3.12 source theorem remains accepted only at paper level.
P6/Cor3.12 unconditional proof: not achieved.

P6: OPEN. No Lean.