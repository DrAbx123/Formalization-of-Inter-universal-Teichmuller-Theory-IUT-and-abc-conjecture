# S2227: literal constant presheaf is likely not a sheaf; correct P needs empty-cover refutation or constant sheaf

Date: 2026-11-02. Status: no proved sheaf property for P0; no completed refutation. The general empty-cover counterexample statement and the exact first missing for the slice site are recorded. No IsStack claim, no fake.

## 1. P0 sheaf issue

P0 is the literal constant presheaf on (Over S)^op with value SignGroup.  On a
site with an empty covering sieve at some object X, P0 is not a sheaf when the
value has two distinct elements: the empty family has every global section as
an amalgamation, so uniqueness fails.

The slice site likely has such an object: the empty scheme over S is an initial
object of Over S, and the empty family is an etale cover of the empty scheme.
This gives a concrete refutation route for P0.

## 2. S2227 statements

File: tmp/sheaf/xif/paper/S2227PConstantSheafCorrectActual.lean

S2227ConstantPresheafNotSheafStatement:
  forall (C) (J) (X), (bottom : Sieve X) in J X ->
    forall {A} (a b : A), a != b ->
      not (Presheaf.IsSheaf J ((Functor.const C^op).obj A)).

S2227SliceEmptyCover S:
  (bottom : Sieve (Over.mk (1 : S))) in
    (etaleTopology.over S) (Over.mk (1 : S)).

S2227FirstMissing S := S2227SliceEmptyCover S.

S2227CorrectPFirstMissing S := S2192HasWeakSheafify S.

The general statement is not proved in this file; the slice empty-cover
membership is also not proved.  Both are exact inputs, not assumed.

## 3. Correct P routes

A. Prove S2227SliceEmptyCover S and the general statement; then P0 is refuted.
B. Use the constant sheaf: S2192HasWeakSheafify S (missing Type sheafification
   API), or a finite coproduct of terminal sheaves (not completed in this file).

The finite coproduct route would require the Sheaf category coproduct of
SignGroup-many copies of the terminal sheaf; this was attempted but not
completed within the compile budget, so it is not claimed.

## 4. Status

| Item | Status |
|---|---|
| literal P0 sheaf property | MISSING / likely false |
| empty-cover counterexample | statement + exact missing |
| constant sheaf P | MISSING HasWeakSheafify |
| finite coproduct P | not completed |
| R representable sheaf | PROVED (S2192/S2206) |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 2cad4c9ea89de483af4b7df257d49c9f666030ff856a92a228ae8a9f07052685
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2227PConstantSheafCorrectActual.olean, size 23352
- axioms: propext, Classical.choice, Quot.sound.
