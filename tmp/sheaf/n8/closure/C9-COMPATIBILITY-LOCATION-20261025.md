# WHERE IS THE QUESTIONED COMPATIBILITY?

Date: 2026-10-25. Status: P6 OPEN. No Lean.
File audited: C9-COR312-FROM-ASSUMPTIONS-20261025.md.

## 0. Answer

The questionable compatibility is exactly Step 3 of that proof:

  APT/SHE + IPL  =>  there exists D0 in O with logVol(D0)=Q.

This is NOT a formal consequence of A1=Theorem3.11, A2=Prop3.9,
A3=Remark3.9.5 as stated. It is the bridge reviewers questioned.

## 1. What A1 actually gives

- multiradial construction algorithm;
- possible output data O in 1,circ U;
- IPL: output data linked to the fixed q-pilot input by full
  poly-isomorphisms of F^value x mu-prime-strips;
- SHE: construction expressible relative to the fixed 1-column structure;
- APT: algorithm is a construction algorithm simultaneously valid in
  domain/codomain, not a set-theoretic region map;
- Ind1/2/3.

None of these says:
  there exists an output D0 whose log-volume is the q-pilot value Q.

The q-pilot is an INPUT, not subject to Ind; O is OUTPUT data subject to Ind.
An object-level poly-isomorphism link is not a numerical value-membership
statement.

## 2. The missing lemma

Compatibility (xi-e/xi-f content):

  C1. There exists an output possibility D0 in O (modulo Ind1/2/3)
      such that logVol(D0)=Q.

Equivalently: Q in R_possible.

A1+A2+A3 alone do not prove C1; they provide the objects and properties,
but not this membership. The source's xi-e says the construction
'constitutes a construction' of Q; xi-f then asserts inclusion. That step
is the compatibility.

## 3. What reviewers objected to

- APT is not a set-theoretic transport, so it does not give an output element;
- SHE is expressibility under the fixed input value, not equality of output;
- IPL links prime-strips/constructions, not the q-pilot value as output;
- closed loop/cQ3/cQ4 yield simultaneous intertwinings, not numerical
  membership;
- Ob9-1 says formal indeterminacies do not affect comparability, not that Q
  is in the possible output set.

So the compatibility is a genuine extra lemma, not an A1-A3 consequence.

## 4. Consequence for the three-assumption proof

The proof C9-COR312-FROM-ASSUMPTIONS is valid only if C1 is added.
Without C1, Step 3 is an assertion, i.e. a named sorry in disguise.
Therefore:

  A1+A2+A3+C1 => Cor3.12

and C1 is exactly the open compatibility/xi-e problem.

P6: OPEN. No Lean.