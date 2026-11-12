# S2234: P0 correct-sheaf decision — empty-cover refutation not completed; correct P still missing

Date: 2026-11-02. Status: no Lean proof of S2227SliceEmptyCover and no completed refutation of P0. R remains an actual sheaf. No fake, no IsStack claim.

## 1. Decision attempt

The literal constant presheaf P0 is expected to be not a sheaf: on a site with an
empty covering sieve at an object X, the empty family has every global section
as an amalgamation, so uniqueness fails when the value has two distinct
elements.

For the slice site, the intended X is an empty-scheme object.  The required
membership is:

S2234SliceEmptyCover S := S2227SliceEmptyCover S
  = (bottom : Sieve (Over.mk (1 : S))) is in
      (etaleTopology S1726K).over S (Over.mk (1 : S)).

This is not proved in Lean.  No refutation is claimed.

## 2. Alternative correct P

- constant sheaf via HasWeakSheafify:
    S2234CorrectPFirstMissing S := S2227CorrectPFirstMissing S
      = S2192HasWeakSheafify S.
- finite coproduct of terminal sheaves: not completed.

No correct P is constructed.

## 3. Actual R

R = (Over.forget S).op >> yoneda.obj S1726AffineOver,
with Presheaf.IsSheaf proof from S2192/S2206.  This part remains actual.

## 4. S2234 file

File: tmp/sheaf/xif/paper/S2234PConstantCorrectActual.lean

definitions:

- S2234SliceEmptyCover S;
- S2234EmptyCoverFirstMissing S;
- S2234CorrectPFirstMissing S;
- S2234P0Sheaf S.

No inhabitant is asserted.

## 5. Status

| Item | Status |
|---|---|
| empty-cover membership | MISSING exact |
| P0 refutation | not completed |
| general empty-family argument | informal only |
| constant sheaf P | MISSING HasWeakSheafify |
| finite coproduct P | not completed |
| R representable sheaf | PROVED |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 02db6db99be9e21070ce625f41502c0fb6af3e64d521561cbd743165eba426b9
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2234PConstantCorrectActual.olean, size 8400
- axioms: propext, Classical.choice, Quot.sound.
