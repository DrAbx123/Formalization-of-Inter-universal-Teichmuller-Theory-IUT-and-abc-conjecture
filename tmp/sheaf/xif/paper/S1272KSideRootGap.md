# S1272: K-side 2l root data — exact first field

Target:

```lean
KSideTwoLRootData T b
```

from `S438QVFamilyKSideCandidateActual`:

```text
root : Completion (qVFamilyKLift T b)
root_pow : root ^ (2 * l.value) = (qVFamilyK T b).q
class_well_defined : Prop
```

## Actual parts

- `qVFamilyKLift`, `qVFamilyKParameter`, `qVFamilyK` are actual
  (`S438`);
- `qVFamilyK_order : (qVFamilyK).order = e * (qVFamily T b).order`, actual;
- `S459KrootCandidateActual` constructs an actual root
  `candidateKRoot : AlgebraicClosure (Completion ...)` with
  `candidateKRoot ^ (2l) = algebraMap (qVFamilyK.q)`, plus `KrootField`
  and `krootCandidate`;
- `S467`/`S472` record the exact order/ramification controls.

Thus the 2l-root exists **only in the algebraic closure**, not in the
completion `Kq`.  There is no actual `KSideTwoLRootData` because its `root`
field must live in `Kq`.

## First exact missing fields

### 1. root_in_completion

```text
root_in_completion :
  ∃ x : Completion (qVFamilyKLift T b),
    algebraMap (Kq) (ACq) x = candidateKRoot
```

Equivalently, the chosen algebraic root lies in the image of the completion.
No theorem in the tree proves this.  Being integral/algebraic over Kq is not
enough: `Completion` is not algebraically closed.

### 2. order/valuation control

```text
twoL_dvd_order_K : (2 * l.value) ∣ (qVFamilyK T b).order
root_valuation_control : Prop
ramification_index_control : Prop
```

`S467` proves only the implication
`(2l) ∣ order_K → l ∣ qVFamilyKRamificationIdx`, and `S472` records that
neither `2 ∣ qVFamily.order` nor `l ∣ ramification` is derived in the repo.

### 3. class_well_defined

`KSideTwoLRootData.class_well_defined : Prop` is an exact remaining field;
it is not a place to hide the root existence.

## Consumer

K-side q_v root used by the Kummer root/quotient nontriviality (S1210)
and the K-side evaluation/root data; no weak Nonempty gate is introduced.

## Exact minimum

```text
root_in_completion
  + twoL_dvd_order_K
  + root_valuation_control
  + class_well_defined
```

Status: exact stop at `root_in_completion`; no fake Completion root, no new
weak Lean file, no compile claim for KSideTwoLRootData.
