# Mod29 factorization actual inputs for localized S2427

Date: 2026-11-06. Sources: S2141D5FactorizationFieldsActual.lean (olean present, nonstale); S2491CycleComputationActual.lean (source only, no olean).

## S2141 actual (olean 1484832 B, nonstale)

Declarations:

```lean
def S2141Factor2 : (ZMod 29)[X] := S2132Factor2
def S2141Factor10 : (ZMod 29)[X] := ...
def S2141Psi5Mod29 : (ZMod 29)[X] := ...
theorem S2141Reduction
theorem S2141ProductSmall
theorem S2141Product
theorem S2141Factor2_natDegree : S2141Factor2.natDegree = 2
theorem S2141Factor10_natDegree : S2141Factor10.natDegree = 10
```

So available actual:
- explicit factor polynomials;
- their product identity with S2132Psi5Z mod 29;
- degrees 2 and 10.

Not actual in S2141 (only Props):

```lean
def S2141IntegerModelRequired : Prop
def S2141QuadraticIrreducibleRequired : Prop
def S2141DegreeTenIrreducibleRequired : Prop
```

These are stated obligations, not proved. `s2141S2057Mod29Data_of` is conditional on them.

## S2491 status: NOT KERNEL VERIFIED

No olean under .lake/build/lib/lean. Source has no real `sorry`/`axiom` declarations; the `axiom` grep hits are only `#print axioms` lines. But without an olean, its claimed proofs of

```lean
S2491Factor2_irreducible
S2491Factor10_irreducible
S2491FactorDegrees
S2491permBar_cycleType_normalized
S2491DedekindFrobeniusCycleType
S2491rootCycleType_of_factorDegrees
```

are unverified and cannot be used as actual inputs.

## What localized S2427 needs

For fbar/factorDegrees on localized (T/P) ring:

1. `fbar` of the localized model f = S2132Psi5Z.map (O_F'[1/10]) at p over 1249/29;
2. separable fbar;
3. explicit factor multiset `factorDegrees (fbar) = {2,10}`;
4. irreducibility of both factors over the actual residue field;
5. identification of the residue field with ZMod 29 (residue degree 1), otherwise the mod29 factorization does not directly transport.

## What is missing

- S2141 fails to provide actual irreducibility of the two factors (Props only).
- S2491 appears to fill this but has no olean; must be compiled/verified first.
- Neither file gives the localized fbar identification/residue-degree-one transport at T/P.

## Exact reuse candidates

If S2491 compiles (EXIT=0, trio axioms):

```lean
S2491Factor2_irreducible : Irreducible S2141Factor2
S2491Factor10_irreducible : Irreducible S2141Factor10
S2491FactorDegrees : factorDegrees ... = {2,10}
S2491ConcreteMod29Factorization : ...
```

Then localized S2427 needs only the fbar/residue identification and transport to T/P.

## Status

- S2141 actual: explicit polynomials, product, degrees; irreducibility Props only.
- S2491: UNVERIFIED (no olean).
- localized S2427 fbar/factorDegrees inputs: PARTIAL.
