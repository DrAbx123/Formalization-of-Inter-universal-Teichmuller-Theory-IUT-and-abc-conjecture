# S2532: S2470RootToRangeTransport ACTUAL

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2532PairTransitiveActual.lean
  SHA256 EA0626977994385F2E24CF6F54488CD47F767989DCFA2662ABB73313F6626B9B
  EXIT=0
  olean SHA256 B7EC2E21FF8BF4AD0379436DD948DF572F0BF7A3E16485DDE6BACDF370FAD80F
  size 162544
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Repaired and compiled. Actual theorems:
- S2532rootSet_eq
- S2532RootEquiv
- S2532rootCycleType_eq
- S2532RootToRangeTransport : S2470RootToRangeTransport
- S2532ExactMissing_of_residueData : S2470ActualResidueData -> S2532ExactMissing
- S2532Target_of_residueData : S2470ActualResidueData -> S2532Target
- S2532Target_of_residueData_via_S2470

Thus the former root-to-range transport gap is CLOSED unconditionally.

## Exact remaining input

S2532ResidueCertificateRequired : Prop := Nonempty S2470ActualResidueData
= S2470ResidueCertificateRequired.

This requires an actual integral model f of a nonzero multiple of psi_5 over
O_{F'}, a maximal prime p of O_{F'} and a prime P of the actual 5-division
field above p such that fbar f p is separable irreducible of degree 12.

The mod-613 Rabin certificate S2540 (S2540F_irreducible /
S2540ResidueCertificate) is the finite-field half; the remaining work is
assembling the actual model/prime data and identifying the reduction.

## Status

- root-to-range transport: ACTUAL (S2532).
- actual residue data: still missing.
- no fake; no sorryAx.
