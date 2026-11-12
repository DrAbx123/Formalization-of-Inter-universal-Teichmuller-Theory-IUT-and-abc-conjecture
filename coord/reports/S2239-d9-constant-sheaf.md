# S2239: Type-valued constant sheaf P — Mathlib API audit and exact first missing

Date: 2026-11-02. Status: no correct P constructed. Mathlib has a plus-construction sheafification instance for Type (max u v), but not directly for the Type-valued slice site needed here. Exact API missing recorded. No fake, no IsStack claim.

## 1. Mathlib audit

Relevant Mathlib file: Mathlib/CategoryTheory/Sites/LeftExact.lean.

It contains:

  instance [PreservesLimits (forget D)] [HasFiniteLimits D]
      [forall X, Small.{t, max u v} (J.Cover X)^op] : HasSheafify J D

and, for D = Type (max u v):

  instance : HasSheafify J (Type (max u v)) := inferInstance.

So Mathlib has a Type-valued plus construction at universe Type (max u v).

For the present slice site S and value Type (universe 0), the instance does not
synthesize.  A direct construction

  HasSheafify.mk' J Type (plusPlusAdjunction J Type)

fails with the exact obligations:
- forall P X R, HasMultiequalizer (R.index P);
- PreservesFiniteLimits (plusPlusSheaf J Type).

These are the precise Mathlib API gaps for the Type-valued plus construction on
the slice site.

## 2. S2239 package

File: tmp/sheaf/xif/paper/S2239PConstantSheafActual.lean

- S2239HasWeakSheafify S :=
    Nonempty (HasWeakSheafify (etaleTopology.over S) Type);
- S2239ConstantSheafFirstMissing S := S2239HasWeakSheafify S;
- S2239FiniteCoproductFirstMissing S :=
    Nonempty (Sheaf (etaleTopology.over S) (Type)).

No P sheaf, no HasWeakSheafify instance is constructed.

## 3. Finite coproduct of terminal sheaf

The alternative route would take SignGroup-many copies of the terminal sheaf in
the Sheaf category.  This requires the coproduct model and the identification
with the constant presheaf; it was not completed in this file.  No claim is made.

## 4. P0 risk

The literal constant presheaf P0 is likely not a sheaf (see S2227/S2234), so the
correct P must be the sheafification/coproduct model, not P0.

## 5. Status

| Item | Status |
|---|---|
| Type-valued sheafification for slice site | MISSING exact |
| HasMultiequalizer API | MISSING |
| PreservesFiniteLimits plusPlusSheaf | MISSING |
| constant sheaf P | not constructed |
| finite coproduct of terminal sheaf | not completed |
| R representable sheaf | PROVED |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: f1b2527e44ee757604b7e63ae61ab295d2154e15a0531df2a47227da070774a1
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2239PConstantSheafActual.olean, size 10120
- axioms: propext, Classical.choice, Quot.sound.
