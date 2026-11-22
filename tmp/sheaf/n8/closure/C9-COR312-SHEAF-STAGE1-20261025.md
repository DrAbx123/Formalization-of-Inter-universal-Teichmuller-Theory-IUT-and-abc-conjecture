# SHEAF Stage1 Node: IUT-III Cor3.12 via C1

Date: 2026-10-25. Status: stage1 conditional; C1 OPEN; no unconditional 3.12.

## Node

id: IUT-III.Cor312.C1-stage1
target: for every admissible initial Theta-data C, -|log Theta| >= -|log q|.
source: IUT III, Corollary 3.12 / Theorem B, proof Step (xi), lines 10641-10715.

## Statement

Q := -|log q| (q-pilot log-volume)
h := -|log Theta| (procession-normalized log-volume of the holomorphic hull
     of the multiradial output possibilities)
C1: Q is in R, the set of possible output log-volumes (mod Ind1/2/3):
    exists output D0 in O, logVol(D0)=Q.
Conclusion: Q <= h.

## Statement dependencies

- q-pilot/Theta-pilot objects (Def3.8)
- multiradial output collection O and Ind1/2/3 (Theorem3.11)
- holomorphic hull and procession-normalized log-volume (Remark3.9.5, Prop3.9)
- R, C1.

## Proof dependencies

- A1 Theorem3.11 (algorithm, O, IPL/SHE/APT, Ind1/2/3).
- A2 Proposition3.9 (log-volume definition/monotonicity).
- A3 Remark3.9.5 (hull, Ob1-Ob9, formal indeterminacies).
- C1 (named gap).

## Natural-language proof (conditional)

1. Fix C. By A1, form O, the collection of possible output data, and the
   hull H of O. By A2/A3, h=logVol(H) and logVol is monotone on regions.
2. Hence for every D in O, logVol(D) <= h. Therefore R subset {x|x<=h}.
3. By C1, there exists D0 in O with logVol(D0)=Q. Hence Q in R.
4. From Q in R and R subset {x|x<=h}, Q<=h.
5. Since Q=-|log q| and h=-|log Theta|, -|log Theta|>=-|log q|.

This proof is conditional on C1. It is otherwise elementary (membership +
monotonicity); it does not prove C1.

## Gap

C1 is OPEN. Evidence:
- 8 independent routes (C9-C1-*.md) show A1+A2+A3 do not imply C1.
- LANA 2026 report states the q-pilot/multiradial compatibility is unproven
  and formulates it as eta_q = eta^anab_S (9-1).
- Minerval claim: same unproven compatibility.
- Joshi arithmetic Teichmuller proves Cor3.12 by a different route; it does
  not establish IUT C1.

## Formalization

Lean stage1: tmp/sheaf/n8/closure/C9Cor312Stage1.lean
- C1 is a hypothesis/definition, not a theorem.
- cor312_of_C1 is proved with no sorry, but is conditional on C1.
- This file is not a proof of Cor3.12.

## Status

statement_compiles: pending Lean build
proof_body_checked: conditional theorem
kernel_closed: only for conditional theorem, not Cor3.12
target_accepted: false
C1: OPEN. No unconditional 3.12. No false closure.