# BUILD INCIDENT: D5 S2446 proof state (no new compilation)

Date: 2026-11-03. Per Lead BUILD INCIDENT instruction, all lake/lean commands
stopped. No compilation attempted after this report.

## Proof-state records

- tmp/sheaf/xif/paper/S2440RootPermCycleCleanActual.lean
  src SHA256: 88E6A0C79E2CD7FFADEAB936C157DC7CC6F887261986A3FABD95EDC2D00F53CC
  olean: exists, SHA256 34F87BFF37C5586CDA751107C7D6F70B544D6DF312A3AEBF1B074643A2F330B9
- tmp/sheaf/xif/paper/S2428FilterBridgeActual.lean
  src SHA256: 487D12CE98D6186F8FB8CF212B9888C476FD715685415F18EAFA780135A1D311
  olean: exists, SHA256 0DE405A566CEB875A110D0F24BEB37E30112F7FA0717DEF6547687820A49DA7B
- tmp/sheaf/xif/paper/S2425PermBarInvarianceActual.lean
  src SHA256: 170F312521AAAD51DAAD0DB7B9EFBAC7245338106D624683C570FB0BA572854E
  olean: exists, SHA256 9476B00F7FD1C7816A68F6456FE94399F13236CBF221BD4527C606C057F1F4D0
- tmp/sheaf/xif/paper/S2420DedekindApplyActual.lean
  src SHA256: 26F53AF2BE29DD0AA0DF26D5D67B43E2F609057BE2CD3987A388B8DCB2AE4393
  olean: exists, SHA256 388DDEBDE81F1AFA4542A616D44C175F3C3DDF9BF626CBD9679FFDF66D054EFE
- tmp/sheaf/xif/paper/S2446D5FinalActual.lean
  src SHA256: 4B4F9FACEC6015988BF08BB8CD77DAC5641E87533F92B67F7F84D2F7844ECB19
  olean: MISSING
- tmp/sheaf/xif/paper/S2427RootPermCycleActual.lean
  src SHA256: 65EA5BCB5978BCCEC4889E159D9535D370A2DCA7E1C632FC7A7C9C9929735B36
  olean: MISSING

## Established before incident (clean)

- S2440RootPermCycleCleanActual: EXIT=0, olean exists, axioms trio,
  no sorryAx. Clean rootPerm/permBar cycle-type transport.
- S2428FilterBridgeActual: EXIT=0, olean exists, axioms trio, no sorryAx.
- S2425PermBarInvarianceActual: EXIT=0, olean exists, axioms trio.
- S2420DedekindApplyActual: EXIT=0, olean exists, axioms trio.

## S2446D5FinalActual: NOT VERIFIED

Source contains:

- s2446FiberEquiv:
    {x : (fbar f p).rootSet E // s2425RootFactor ... x = b}
    ~= {y : E // minpoly F y = b.1}
  forward x |-> x.1.1; backward y |-> <y.1, rootproof>; rootproof uses
  Polynomial.mem_normalizedFactors_iff, minpoly.aeval, b.1 | fbar, and
  Polynomial.mem_rootSet'.
- s2446Fiber_card:
    Fintype.card fibre = b.1.natDegree
  intended via Nat.card_congr s2446FiberEquiv + s2408FiberSet_ncard.

A previous compile of this source (before the incident) failed at the
right_inv field; that was corrected to rfl in the source.  The subsequent
verification attempt hit missing Mathlib/toolchain oleans, so the corrected
source has NOT been compiled and is NOT accepted.

## Exact remaining

1. Re-run compile gate after build coordinator clears Mathlib artifacts.
2. If s2446FiberEquiv/s2446Fiber_card pass, continue with:
   - each-fibre transitivity via S2339FrobTransitive;
   - S2428 filter bridge;
   - S2440 cycle transfer;
   - cycleType_eq_fiber_sizes application to obtain
       rootCycleType = (factorDegrees (fbar f p)).filter (· != 1).
3. Do not use S2427 (sorryAx).

## Status

- D5 corrected theorem: NOT ACCEPTED.
- No fake; no new compilation after incident notice.
- S2446 source SHA recorded above.
