# S1303: SourceProcessionCapsuleContract integral log-shell audit

Date: 2026-10-30. Report + new actual Lean file; no PUnit/Q-span surrogate.

## 1. S1270 IQSpan is a reduced Q-vector shell

`S1270NontrivialCapsuleActual.actualLogShellFamily`:

```lean
Shell := fun _ vQ v => (actualLocalLogShellDatum I vQ v).IQSpan
```

and

```lean
actualIQSpan_eq_span_integralLogShell :
  IQSpan = Submodule.span ℚ (integralLogShell ... : Set K)
```

`IQSpan` is `Submodule.span ℚ D.logShell` (SourceLogShellCarrier:238), a
ℚ-vector space.  It is **not** the paper's integral log-shell: it forgets the
`Z_p`/integral lattice and keeps only the rational span.  S1270 is therefore a
reduced Q-vector capsule, not an original-object construction of the integral
log-shell module.

Its `actualPolyIso` also scales by `2 : ℚ`, i.e. it exists only because 2 is a
unit in ℚ; this cannot replace an integral-lattice poly-isomorphism.

## 2. Actual integral lattice available in the tree

`IntegralLogShellLattice.lean` constructs:

```lean
integralLogShellLattice : Submodule ℤ_[p] K
```

with carrier exactly `integralLogShell`, finite/free over `ℤ_[p]`, compact,
and full rational-padic span.  This is the actual integral lattice, not a
Q-span model.

## 3. New actual construction (S1303)

`S1303IntegralLogShellContractActual.lean` (EXIT=0, no sorry) builds:

- `actualIntegralLogShellLattice vQ v : Type := ↥(integralLogShellLattice ...)`
  at every actual rational valuation `vQ` and actual finite place
  `v : FinitePlaceAtPrime Fmod vQ.1`;
- a `Module ℤ` instance via
  `Module.restrictScalars ℤ ℤ_[vQ.1]`;
- `actualIntegralLogShellFamily : LogShellFamily ℤ (actualPlace I) j`
  with the actual integral lattice as `Shell`;
- `actualIntegralPolyIso` with `labelPerm := Fin.revPerm` and each
  `shellEquiv := -1` (an actual integral-lattice automorphism);
- `actualIntegralCapsuleContract :
  SourceProcessionCapsuleContract ℤ l V I` over the actual
  `ActualValuation` and actual finite-place fibers.

This uses no `PUnit`, no `IQSpan`, and no rational span as the shell module.
The shell carrier is the genuine `integralLogShellLattice`.

## 4. Exact remaining structural field

The contract has a **single** coefficient ring `R`.  The actual integral
lattices are `ℤ_[p]`-modules with `p = vQ.1` varying over rational valuations,
so no single `ℤ_[p]` acts on all fibers.  S1303 therefore uses `R = ℤ`: the
integral lattice is retained, but only its `ℤ`-linear structure is uniformly
recorded; the `ℤ_[p]`-linear structure is per-fiber and not a contract field.

Exact first structural gap for the paper object:

```lean
R : VQ → Type
[∀ vQ, CommSemiring (R vQ)]
-- and for each fiber:
Module (R vQ) (Shell i vQ v)
-- with R vQ = ℤ_[vQ.1] for the integral lattice
```

i.e. the capsule contract needs a valuation-dependent coefficient ring (or an
explicit `ℤ_[p]`-linear polyIso family) to express the actual integral
`Z_p`-module structure uniformly.  A fixed `R = ℤ` retains the lattice carrier
but not the full `Z_p`-linear object; a fixed `R = ℤ_[p]` cannot cover
`p ≠ vQ.1`.

## 5. PolyIso

`actualIntegralPolyIso` is actual and integral:

- label permutation `Fin.revPerm` is an actual nonidentity permutation;
- `shellEquiv = -1` is an integral-lattice automorphism (`LinearEquiv.neg ℤ`);
- it does not use multiplication by 2 or rational scaling.

The paper's poly-isomorphism also involves the label/place transport; S1303
supplies an actual integral action but not a proof of agreement with the
paper's specific poly-isomorphism.  That agreement (or the source construction
of the poly-isomorphism) remains exact.

## 6. Conclusion

- S1270 is simplified: `IQSpan = Q-span` of the integral log-shell; not the
  original integral `Z_p` lattice module.
- Actual integral lattice exists and is used in S1303; the new contract keeps
  the genuine lattice carrier over `R = ℤ`.
- Exact remaining field: valuation-dependent coefficient ring / uniform
  `Z_p`-linear structure, and the source/polyIso agreement.
- No PUnit/Q-span surrogate in S1303; EXIT=0 report.
