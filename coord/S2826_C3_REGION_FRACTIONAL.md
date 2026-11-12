# S2826 — C3 region vs fractional-lattice region

Date: 2026-11-07
Target: prove
`actualC3LogShellTensorRegion C3 = ((F c) * O_hol : Set ...)`
and then apply the S2818 factor formula.
Result: **not actual**; precise first error and exact blocker recorded.
No fake equality, no axiom.

## 1. S349 gives the lattice, not the fractional-lattice model

`tmp/sheaf/xif/paper/S349C3TensorLatticeRegionActual.lean` proves:

```lean
theorem actualC3LogShellTensorRegion_eq_tensorLogShellRegion :
    actualC3LogShellTensorRegion C3 =
      tensorLogShellRegion (p := C3.p)
        (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i)

theorem actualC3LogShellTensorRegion_subset_latticeRegion :
    actualC3LogShellTensorRegion C3 ⊆
      actualC3LogShellTensorLatticeRegion C3
```

and defines the **corrected** region

```lean
noncomputable def actualC3LogShellTensorLattice :
    Submodule ℤ_[C3.p] (C3LogShellTensorBlock C3) :=
  tensorLogShellLattice (A := fun i => C3LogShellFiber C3 i)
```

S349 explicitly says the paper tensor packet is the `Z_p`-**span** of the pure
tensors, not the pure-tensor image:

> “The corrected paper unit region: the actual tensor integral lattice ..., not
> merely the pure-tensor image.”

So S349 gives only the *lattice* region and the inclusion of the pure image;
it never identifies either with `(F c) * O_hol`.

## 2. Actual partial results (compiled)

`tmp/sheaf/xif/paper/S2826C3RegionFractionalLatticeIdActual.lean`

```text
src 3195 B
SHA256 718f6e87b9ab0623850adddd8212ce33a1040e415f901b94627bb64918833ce9
olean 58824 B
SHA256 d01d08f380c89d5ac3dd020f88d064b14a8d372011b27ab9be1d8f062b191452
EXIT=0
AXIOMS [propext, Classical.choice, Quot.sound]
QUEUED
```

Contents:

```lean
def S2826C3RegionFractionalLatticeId (c : C3.tensorIndex -> Real) : Prop :=
  actualC3LogShellTensorRegion C3 =
    ((F c * O_hol : Submodule ℤ_[C3.p] ...) : Set ...)

theorem S2826_region_eq_tensorLogShellRegion : ...  -- re-export of S349

theorem S2826_region_subset_latticeRegion : ...    -- re-export of S349

theorem S2826_fractionalLatticeId_implies_lattice_subset
    (h : S2826C3RegionFractionalLatticeId C3 c) :
    ((F c * O_hol : Submodule ...) : Set ...) ⊆
      actualC3LogShellTensorLatticeRegion C3
```

The last is the only actual consequence of the target: it would force the
fractional lattice to be contained in the corrected log-tensor lattice.

## 3. Precise first error

Attempting the target directly with `rfl` fails:

```text
Tactic `rfl` failed: The left-hand side
  actualC3LogShellTensorRegion C3
is not definitionally equal to the right-hand side
  ↑(arithmeticTupleFractionalLattice C3.tensorPlaces C3.tensorTuple c *
      arithmeticTupleHolomorphicLattice C3.tensorPlaces C3.tensorTuple)
```

After rewriting by
`actualC3LogShellTensorRegion_eq_tensorLogShellRegion`, the goal becomes

```lean
tensorLogShellRegion (A := fun i => C3LogShellFiber C3 i) =
  ((F c * O_hol : Submodule ...) : Set ...)
```

and there is no theorem relating `tensorLogShellRegion` to
`arithmeticTupleFractionalLattice`.  This is the first precise missing step.

## 4. Exact blocker: two missing identifications

The target factors through two statements, both absent:

1. **Pure image = lattice region**

```lean
actualC3LogShellTensorRegion C3 =
  actualC3LogShellTensorLatticeRegion C3
```

S349 proves only `⊆`, and explicitly distinguishes the pure image from the
`Z_p`-span.  No equality theorem exists.

2. **Log-tensor lattice = fractional lattice translate**

```lean
actualC3LogShellTensorLattice =
  arithmeticTupleFractionalLattice C3.tensorPlaces C3.tensorTuple c *
    arithmeticTupleHolomorphicLattice C3.tensorPlaces C3.tensorTuple
```

`actualC3LogShellTensorLattice` is `tensorLogShellLattice`, the `Z_p`-span of
the local `integralLogShell` sets.  `arithmeticTupleFractionalLattice` is built
from `padicFractionalLattice` p-power lattices.  No theorem identifies these;
indeed `integralLogShellLattice` is a unit-log lattice containing the integers,
not generally a p-power fractional lattice.

Even the weaker lattice-to-fractional identification is missing; the pure-image
version is strictly stronger.

## 5. Consequence for SG3b/SG3a

The S2818 factor formula

```lean
arithmeticTupleNormalizedLogVolume ... ((F c) * O_hol) =
  -((∑ i, c i) * Real.log p)
```

cannot be applied to `actualC3LogShellTensorRegion` without these missing
identifications.  Do not assert `S2826C3RegionFractionalLatticeId`.

The only safe actual statement is the implication in
`S2826_fractionalLatticeId_implies_lattice_subset`, plus the S349 inclusion.

## 6. Status

```text
S349 pure region = tensorLogShellRegion          ACTUAL
S349 pure region ⊆ lattice region                ACTUAL
target region = (F c) * O_hol                    MISSING (rfl fails)
pure region = lattice region                     MISSING
log lattice = fractional lattice                 MISSING
S2818 factor formula for fractional lattice      ACTUAL
```

No fake equality, no axiom beyond the permitted trio.
