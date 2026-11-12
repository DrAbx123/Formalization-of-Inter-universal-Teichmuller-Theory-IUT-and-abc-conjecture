# S1865: coherent coproducts from the coherent affine bridge; exact first missing

Date: 2026-11-01

Lean: `tmp/sheaf/xif/paper/S1865CoprodApexActual.lean`

Namespace: `LeanFormal.IUT.XiFPaper.S1865CoprodApexActual`

EXIT=0

Source:

* bytes: 11647
* SHA256: `A0D9B5E5BBEBAD5720925611615CD8FD27E278A58FE4335887E53D547F2B4AF3`

Olean:

* path: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1865CoprodApexActual.olean`
* bytes: 133016
* SHA256: `D67A682E13A663AE8529F66A26BD49B8F118781CACFB81233CD9A57CE12D74C3`

Independent import check: `tmp/sheaf/xif/paper/S1865Check.lean` imports the olean and
rechecks the two target-universe coproduct instances, S1833FirstMissing, and the
essential apex.  EXIT=0, same axiom trio.

## Verdict

1. **Coherent finite coproducts are constructed** at both S1854 universes:

   * `S1865CoherentHasFiniteCoproducts (h : S1878EssSurj)` on the induced
     coherent category;
   * `S1865Coherent11HasFiniteCoproducts` on `S1854CoherentCategory11`;
   * `S1865Coherent01HasFiniteCoproducts` on the target `S1854CoherentCategory01`.

   Fullness `S1878Full` is now unconditional (`S1878Full_proof` in the updated
   S1878), so the only coherent-affine input is `S1878EssSurj`.

2. **Weak finite coproducts and S1833FirstMissing** are derived from
   `S1878EssSurj` and `S1871EssSurj` (essential surjectivity of the coherent
   subcategory):

   * `S1865WeakHasFiniteCoproducts`;
   * `S1865WeakEquivTarget : Nonempty (S1728Cover ≌ FiniteEtaleCover (Spec R'))`;
   * `S1865WeakAlgEquiv : Nonempty (S1728Cover ≌ (FiniteEtale R')^op)`;
   * `S1865S1833FirstMissing`.

3. **The strict S1854 coproduct apex condition is not the clean first missing.**

   `S1854CoproductApexCoherent h0 h2` asks the arbitrary `Classical.choice`
   representatives of `HasInitial`/`HasBinaryCoproducts` to be *literally*
   coherent.  `HasColimit` is a `Prop` class whose witness is extracted by
   `Classical.choice`; there is no definitional control over the chosen apex.
   The choice-free statement is

   `S1865EssentialCoproductApex` (a coherent cover merely isomorphic to the
   chosen apex), and it is **equivalent to `S1871EssSurj`** in the precise
   sense `S1865EssentialCoproductApex_of_essSurj`.
   The strict condition implies the essential one
   (`S1865StrictApex_implies_essential`), but not conversely in general:
   the missing extra content is the literal equality of the chosen witness.

4. **The strict S1856CoproductFirstMissing would follow from the equality
   version of coherent essential surjectivity**
   (`S1865S1856CoproductFirstMissing_of_eqSurj`).  That equality version is
   false: `S1871NotForallCoherentEq` (S1871) from S1852's doubled cover.
   This does not refute the strict S1856 statement, but it shows that the
   natural route to it requires a false statement, and it isolates the extra
   content as a property of the chosen `Classical.choice` witness.

## Exact first missing

```
S1878EssSurj   -- every finite etale cover of Spec R' is the affine model
               -- of a coherent cover (the inverse construction)
S1871EssSurj   -- every weak cover is isomorphic to a coherent cover
               -- (equivalently S1871StrongSliceEquiv)
```

Neither is proved here.  Together they give the coherent coproducts, the
weak coproducts, the affine equivalence of the weak category, and
S1833FirstMissing.  `S1878Full` is no longer an input.

The parallel S1897 reduces `S1878EssSurj` further to `S1897FirstMissing`
(a strong finite-etale structure on the representable extension cover
`S1897ExtMap C` at the non-identity test points).  Consequently

```
S1865Coherent01HasFiniteCoproducts (S1897EssSurj_of_extensionData h)
```

closes the coherent coproducts from `S1897FirstMissing`, and the honest frontier
is `S1897FirstMissing` together with `S1871EssSurj`.

## Axiom audit

Every `#print axioms` in the file and in the independent check reports only

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, new `axiom`, `native_decide`, `Shrink`, `ULift`,
`PLift` or `PUnit`.  The words occur only in the honest-boundary docstring.

## Status

* statement_compiles = yes
* proof_body_checked = yes
* kernel_closed = yes (conditional theorems; no unproved inhabitant asserted)
* target_accepted = false (S1878EssSurj and S1871EssSurj remain open)

## Next executable step

Prove `S1878EssSurj`: from a finite etale cover X -> Spec R', build the
representable cover with source Y(X) and strong finite-etale structure, and
identify its affine model with X.  Alternatively prove `S1871EssSurj` via
`S1871StrongSliceEquiv` (realize a strong finite-etale structure on the
slice-isomorphic map).  Either closes one of the two exact inputs.