# C9 no-sorry audit: SourceInputBinding

Task: task-482 (No-sorry SourceInputBinding). Owner: volumedet. Date:
2026-10-25. Audit only; no fake/axiom/toy. Target file:
`tmp/sheaf/n8/closure/SourceInputBinding.lean`. Deliverable: this MD.

## 0. Result

The file contains exactly one `sorry`, in

    theorem sourceInputBinding_nonempty (I : OriginalInput ...) :
      Nonempty (SourceInputBinding I)

It is **not provable from existing project declarations**. No real sorry in this
file is replaceable by a proof. The target file is left unchanged
(87 lines, SHA256 8226bb0a0210aa9133b1376238de1c553a62b21f5d4be8837ca7933ce1436404,
the same SHA recorded in the audit ledger).

Compile with the requested serial wrapper:

    pwsh -File tmp/n8-20261018/lead/lean-serial.ps1 env lean -j1 -R D:/lean
      tmp/sheaf/n8/closure/SourceInputBinding.lean
    EXIT=0

Output: only linter warnings (duplicated namespace, declaration uses `sorry`).
`statement_compiles=true`; `proof_body_checked=false`; `kernel_closed=false`;
`target_accepted=false`.

## 1. The exact theorem and its required fields

`SourceInputBinding I` has one field `place : SourcePlaceRealization I`.
`SourcePlaceRealization I` requires:

1. `placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)`;
2. `selected : V`;
3. `selected_realization : I.SourceImageRealization selected`;
4. `fiberMonEquiv : ∀ (n m : Int) (v : V),
      (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)`.

To prove `sourceInputBinding_nonempty` one must construct all four. None is
available from the current `OriginalInput` or its imports.

## 2. Why each field is not derivable

### C1-a: placeEquiv

`OriginalInput` fields are exactly
`initial : SourceDefinition31Data`, `family : SourceHodgeTheaterFamily l V`,
`index_equiv`, `arithmetic_alignment` (AUDIT_LEDGER 2026-10-23 entry). There is
no field or theorem linking the arbitrary type `V` to
`NumberFieldPlaceIndex (Fmod)`. `SourceHodgeTheaterFamily` has no place
equivalence either; `HodgeTheater`/`FPrimeStrip` are indexed by arbitrary `V`.

Moreover this is not merely missing: for `V = Empty` no such equivalence can
exist, since `NumberFieldPlaceIndex` of a number field has an infinite place.
Thus the unconditional statement `∀ (V) (I), Nonempty ...` is incompatible
with the empty-`V` instance of the current input contract. The exact fix is to
add the actual place equivalence to the source input/target (C1-a), not to
invent a proof.

### C1-e: selected : V

There is no `Nonempty V` field/theorem. The selected place must come from the
source input; `OriginalInput` does not provide it. (The separate
`SourceDefinition31Data.selectedPlaces` is not identified with `V`.)

### C1-d: selected_realization

`SourceImageRealization v` is a structure requiring

* `posRealAction : Multiplicative ℝ →* (I.primeStripAt 0 0).Mon v`, and
* `degree_of_q : logDegreeAt ... (posRealAction q) = Real.log q`.

There is no constructor/existence theorem for this structure in the project.
The `Mon v` of an arbitrary `FPrimeStrip` is an arbitrary `CommMonoid` with a
degree homomorphism; it is not known to receive `Multiplicative ℝ`. Inventing
such a homomorphism would be a free donor and a target change.

### C1-b: fiberMonEquiv

The required comparison is with the actual production value groups
(`finitePlaceValueGroup = Multiplicative ℤ`, `archimedeanValueGroup =
Multiplicative ℝ`). No theorem compares an arbitrary `(I.primeStripAt n m).Mon v`
to either group. `FPrimeStrip.Mon` is arbitrary; the `SourcePlaceValueGroup`
definition only selects a codomain, it does not construct the equivalence.

### C1-g1/C1-c

These are deliberately not fields of `SourceInputBinding`; the global
Frobenioid and Prime/rho comparison remain separate obligations. They are not
available as proof donors either.

## 3. What was checked

- Target file: one `sorry`, line 85.
- `OriginalInput` field list: no place/selected/realization/fiber data.
- `SourcePlaceRealization` field types: all four are required.
- `SourceImageRealization`: structure with no existence theorem.
- `SourcePlaceValueGroup`: codomain definition only; no `Mon v` identification.
- `lean-serial` compile: EXIT=0 with only sorry/linter warnings.

No source declarations were found that discharge any required field.

## 4. Why no replacement was made

Replacing the `sorry` with any of the following would be fake/toy/axiom or a
target change:

- an arbitrary `placeEquiv` from `V` to the place index;
- an arbitrary `selected : V`;
- an arbitrary `SourceImageRealization`;
- an arbitrary monoid equivalence for `fiberMonEquiv`;
- adding a free field to `SourceInputBinding` or `OriginalInput`.

None is justified by actual project declarations. The task says replace only
provable sorries; there are none here. The exact obstruction is the four C1
source fields above.

## 5. Exact next step (outside this task)

To remove the sorry, one must first construct or add to the actual source input:

1. the actual place equivalence `V ≃ NumberFieldPlaceIndex Fmod` (C1-a);
2. the C1-selected place `v` (C1-e);
3. the actual source image realization at `v` (C1-d);
4. the fiber value-group comparison (C1-b).

Alternatively, the target must be restated for the actual
`NumberFieldPlaceIndex`-indexed source carrier, not arbitrary `V`. Both are
target/input decisions, not proof repairs in this file.

## 6. Classification

PROVED/VERIFIED:

- Only one sorry exists in the target file.
- It is the C1 `sourceInputBinding_nonempty` theorem.
- None of its required fields is derivable from current declarations.
- Compile EXIT=0, with `sorry` warning; statement_compiles only.

NOT PROVED:

- `sourceInputBinding_nonempty`; C1-a/C1-b/C1-d/C1-e.

MISSING/TARGET CHANGE:

- actual place equivalence, selected place, source image realization, fiber
  monoid comparison.

## 7. Status

No file edit was made; no fake/axiom/toy introduced. The sole sorry is a real
C1 obstruction, not a mechanical omission. `target_accepted=false`; C1 remains
open.
