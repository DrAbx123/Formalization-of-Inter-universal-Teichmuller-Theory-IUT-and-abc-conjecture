# S1404: x-coordinate / point-level omega integration

Date: 2026-10-31 (Asia/Shanghai).
File: `tmp/sheaf/xif/paper/S1404XOmegaIntegrationActual.lean`

## Result

- `lake env lean` EXIT=0, no `sorry`/`admit`/`axiom`/`opaque`/`native_decide`.
- Axiom footprint of every exported theorem:
  `propext`, `Classical.choice`, `Quot.sound` (checked by `#print axioms` in the file).
- Source SHA256: `1F3B0C9226834AFDE327FF9522786492C7473CEDBCB3FC4A80AACAA09CFD618F`
- Olean SHA256: `A8AADF825C8F9D7D815588D1A554D29AA79D1C03C440FDB56764022475B694B0`
- Source size: 16226 bytes; olean 1847168 bytes.

## What is actual (proved in this file)

1. `omegaFormula_zero`: the omega identity at `n = 0` (vacuous, since `psi_0 = 0`).
2. `omegaFormula_one`: the omega identity at `n = 1` (`wCoord(P) = psi_2(P)`).
3. `omegaFormula_two`: the omega identity at `n = 2`,
   `wCoord(2P) = psi_4(P) / psi_2(P)^4`, via the tangent computation.
4. `omegaFormula_neg`, `omegaFormula_neg_iff`: invariance under `n -> -n`.
5. `omegaFormula_all_of_pos`: all-integer omega input follows from the
   positive-integer input (using 1, 3, 4 and the zero case).
6. `xCoordinateFormula_strong_of_omega`: if omega holds for every integer,
   then for every `N >= 1` and every nonsingular `P = (x,y)` with
   `psi_1(P), ..., psi_{N+1}(P) != 0`,
   `x(N . P) = Phi_N(x) / psi_N(P)^2`.  Proof: strong induction using
   `xCoordinateFormula_step`, with base cases 1 and 2.
7. `xCoordinateFormula_strong_of_omegaInput` and
   `xCoordinateFormula_strong_of_omegaInput_int`: the same statement via the named
   positive input `S1404OmegaInput`, for `N : Nat` and `n : Int` respectively.

## Exact remaining input

```lean
def S1404OmegaInput : Prop :=
  forall n : Int, 1 <= n -> S1372OmegaFormula W n
```

and, for the known Mathlib 4.32.2 TODO,

```lean
def S1404EllipticNetInput : Prop :=
  forall x y : K, S1372EllipticNetAtPoint W x y
```

`S1372EllipticNetAtPoint` is `IsEllipticNet (fun n => psi_n(x,y))`; the theorem
`IsEllipticNet (normEDS ...)` is an explicit TODO in the local
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.  This file does not assume it.

## Exactness caveat: the nonvanishing hypothesis cannot be dropped by this induction

`xCoordinateFormula_step` requires `psi_k(P) != 0` for all `1 <= k <= n+1`,
not only `psi_n(P) != 0`.  The target `S1372XCoordinateFormula W n` only assumes
`psi_n(P) != 0`.  The two are not equivalent: for a point `P` of order 5,
`psi_5(P) = 0` while `psi_6(P) != 0`; the target at `n = 6` is still
mathematically valid, but the affine induction cannot start because `psi_5` vanishes.
Therefore this file proves the strong statement, not the weak target, and records the
nonvanishing elimination as part of the exact last step.  Removing it needs the global
function-field/Jacobian multiplication formula (Mathlib PR `ZSMul`,
`zsmul_eq_smulEval`), not the affine recurrence.

## Relation to the parallel S1377 omega attempt

`tmp/sheaf/xif/paper/S1377OmegaFormulaActual.lean` (maintained by another process)
attempts the net -> omega simultaneous induction and has the same strong nonvanishing
hypothesis.  It was **not imported here** and is not cited as closed: during this task it
did not produce a clean olean (debug copies contain a `sorry` at the final `w`-step).
S1404 is independent of it and consumes only `S1372XCoordinateFormulaActual`.

## Out of scope (respected)

No separability, root count, xRep fibre bound, torsion cardinality or zero criterion was
touched.  S1392/S1393 remain the other agents' work.

## Executable next step

Prove `S1404OmegaInput`.  A concrete route is to port the Mathlib PR
`DivisionPolynomial/ZSMul.lean` statement `zsmul_eq_smulEval` (or its affine
`zsmul_point_eq_smulX_smulY` form) to this Mathlib pin, then specialize at any
nonsingular point with `psi_n(P) != 0`; this also removes the nonvanishing caveat.
`S1404EllipticNetInput` plus the simultaneous induction closes the strong version
only.
