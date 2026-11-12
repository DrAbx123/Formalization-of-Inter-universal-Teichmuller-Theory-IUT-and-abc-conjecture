# S1833: actual S1728 cover category — finite coproducts from the affine comparison; exact first missing

Date: 2026-11-01

Lean: `tmp/sheaf/xif/paper/S1833ActualCoverCoproductsActual.lean`

Namespace: `LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual`

EXIT=0

Source:

* bytes: 17379
* SHA256: `537B336E2CEEF2161123D2675D0C9152B772D690CEF7DC9D7B463C38A917E25A`

Olean:

* path: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1833ActualCoverCoproductsActual.olean`
* bytes: 70032
* SHA256: `BB91D8A0F0657B0B4022792524379B82DA1F875852C972E6E0AF6650DC72F284`

Independent import check: `tmp/sheaf/xif/paper/S1833Check.lean` imports the
olean, reprints the key types and the axiom sets.  It compiles with EXIT=0 and
the same axiom trio.

## Verdict

`HasFiniteCoproducts` on the actual S1728 category is **not** constructed
unconditionally.  It is constructed here from one explicit missing comparison,
and the exact first missing is named:

```
S1833FirstMissing : Prop := S1743SliceFunctorMissing
```

i.e. the existence of a fully faithful, essentially surjective comparison
functor from the actual cover category to the affine finite-etale slice
`S1733Slice`.  The file proves

* `S1833FirstMissing ↔ S1733CoverSliceEquivalence` (S1733's target);
* `S1833FirstMissing ↔ S1833ActualAffineEquivalenceMissing`, which is exactly
  `Nonempty (S1728ActualCategory11 ≌ (CommAlgCat.FiniteEtale R')ᵒᵖ)`;
* `S1833ActualAffineEquivalenceMissing ↔ S1825AffineEquivalenceMissing` and
  `↔ S1778AffineEquivalenceMissing`;
* `S1833ActualAffineEquivalenceMissing ↔ S1777TargetEquivalence` (definitional);
* S1743's stronger `S1743CoverSliceComparison` (with the explicit object map)
  implies `S1833FirstMissing`.

Thus the coproduct construction itself is not the first missing: the first
missing is the stack-level cover/slice comparison.  In direct geometric terms,
the upstream blocker is source representability of a cover by its identity-point
affine model; S1831 proves that the recorded `TwoPullbackWitness` is too weak
for the genuine 2-universal property and names that statement
`S1831FirstMissing`.

## What is constructed conditionally

From an affine equivalence `e : S1728ActualCategory11 ≌ (FiniteEtale R')ᵒᵖ`:

1. `S1833InitialObj e : S1728Cover` with
   `S1833InitialObj_isInitial e : IsInitial (S1833InitialObj e)`.
2. `S1833CoproductObj e A B : S1728Cover`, the binary coproduct object.
3. `S1833CoproductCofan e A B : BinaryCofan A B` and
   `S1833CoproductCofan_isColimit e A B : IsColimit (...)`, the full binary
   coproduct universal property.
4. `S1833HasFiniteCoproducts_of_affineEquiv e : HasFiniteCoproducts S1728Cover`,
   via the standard initial + binary-coproduct construction
   (`hasFiniteCoproducts_of_has_binary_and_initial`).
5. `S1833HasFiniteCoproducts_of_firstMissing h`, from the exact first missing.
6. `S1833FiniteCoproductObligationActual_of_firstMissing h`, closing S1762's
   exact `S1762FiniteCoproductObligationActual`.

Bonus (same affine equivalence, no extra missing input):

7. `S1833HasPullbacks_of_affineEquiv e` and
   `S1833HasFiniteLimits_of_affineEquiv e`; the latter uses S1762's
   unconditional terminal object.  Hence S1762's pullback obligation and
   finite-limit field are also closed conditionally.
8. `S1833PreGaloisCategoryOfFirstMissing h hQuot hMono`: the actual
   pre-Galois obligation from the exact first missing, the quotient field and
   the mono/direct-summand field.  The pullback and coproduct inputs of S1762's
   assembly are discharged.

## Direct disjoint-union route

The requested direct route (disjoint union of the two cover source stacks,
finite etaleness of the inclusions, initial object, quotient universal property)
is not used and no part of it is faked.

* Mathlib v4.32.2 has no closure of `Pseudofunctor.IsStack` under pointwise
  coproducts, and no stackification/coproduct of Cat-valued stacks.  The tree
  has no such construction either.
* The recorded `TwoPullbackWitness` is too weak to identify a cover source with
  its affine model (S1831 / S1827 / S1801); source representability is the
  first geometrical missing statement on that route.
* The affine route below bypasses the stack coproduct entirely: all coproducts
  are done on the algebra side, where they already exist, and transported
  across the one missing comparison.

## Axiom audit

Every `#print axioms` in the file and in the independent check reports only

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no new `axiom`, no `admit`, no `native_decide`, no `Shrink`,
`ULift`, `PLift` or `PUnit` in the code.  The words occur only in the
honest-boundary docstring.

## Dependency versions

* S1825 olean: 2026-11-01 02:48:41 (137104 bytes)
* S1777 olean: 2026-11-01 02:56:44 (325000 bytes)
* S1809 olean: 2026-11-01 02:35:36 (77592 bytes)
* S1762 olean: 2026-11-01 02:34:34 (114136 bytes)
* S1743 olean: 2026-11-01 00:36:58 (235728 bytes)

## Status

* statement_compiles = yes
* proof_body_checked = yes
* kernel_closed = yes
* target_accepted = false (conditional; exact first missing named, not proved)

## Next executable step

Prove `S1743SliceFunctorMissing` (equivalently `S1733CoverSliceEquivalence`
or the affine equivalence).  The shortest known reduction is S1831's
`S1831FirstMissing`: the identity-point base-change square must be a genuine
2-pullback (source represented by its affine model).  After that, the present
file yields S1762's coproduct and pullback fields, finite limits, and the
pre-Galois assembly with only the quotient and mono/direct-summand fields left.
