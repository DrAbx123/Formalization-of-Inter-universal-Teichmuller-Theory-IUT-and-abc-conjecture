# S1996: actual local decorations for the S1992 rebased family

Source: tmp/sheaf/xif/paper/S1996LocalDecorationsActual.lean
OLean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1996LocalDecorationsActual.olean

## Build

- Command: `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1996LocalDecorationsActual.olean tmp/sheaf/xif/paper/S1996LocalDecorationsActual.lean`
- EXIT = 0
- Compile log: tmp/sheaf/xif/paper/logs/S1996.compile.log (no error/sorry/warning lines)
- Source SHA256: 0FB1099CB3BB0496D82834C698A671BE82128A983D72FC32BD252635D77A0747
- OLean SHA256: 91BA614798A0B3BB87CB85F2F004C545E195AEC49ACC5065C114D03CC3693246
- Source bytes: 18920; OLean bytes: 578328

## What is constructed (kernel-checked)

1. `sqrt5` in `AlgebraicClosure Q_5` with `sqrt5 ^ 2 = 5`; `X^2 - 5` is
   irreducible over `Q_5` by valuation parity.
2. A non-identity local Galois automorphism `swapSqrt5` with
   `swapSqrt5 sqrt5 = -sqrt5`.
3. Actual units `decorationUnit a = 1 + a * sqrt5` of the local valuation
   ring, for every `a : Int`, with explicit inverse and a proof that
   `decorationUnit` is injective.
4. The genuine non-identity unit automorphism
   `swapSqrt5UnitAut : MulAut (LocalOFieldUnits 5)`, and the theorem
   `swapSqrt5UnitAut_not_leftTranslation` that it is not left translation by
   any unit.

## The obstruction to the proposed construction

For any group `G`, a `MulAut G` whose underlying function is `u -> c * u`
exists only when `c = 1` (`mulAut_mulLeft_eq_one`,
`no_mulAut_mulLeft`).  Thus the suggested `alpha_c : u -> c * u` is not a
`MulAut` of `O^×` when `c != 1`; it is a set permutation, not a group
automorphism.  The non-Galois-invariant units `1 + a * sqrt5` are real, but
they cannot be used as unit automorphisms by left multiplication.

## Exact first missing

- `S1996UnitDecorationFamily`: an infinite family of genuine
  `MulAut (LocalOFieldUnits 5)` whose conjugates of the actual local Galois
  action are pairwise distinct.  No inhabitant is constructed; in particular
  the conjugate action of the one nontrivial automorphism
  `swapSqrt5UnitAut` is not proved to differ from the original action.
- `S1996LocalFPrimeStripFamily`: the strip-level datum — an infinite family
  of pairwise distinct F-prime-strips, each linked to `localOFieldStrip`,
  indexed by an equivalence to `SourceTheorem311Index` (`Int × Int`), with
  the core member equal to `localOFieldStrip`.
- Necessity is proved: every `S1992RebasedLocalFamily D` yields a
  `S1996LocalFPrimeStripFamily` (`toLocalFPrimeStripFamily`).

No `sorry`, `axiom`, `admit`, `True`/`PUnit` slot, empty type or arbitrary
inhabitant is used.  Axiom probes only show `propext`, `Classical.choice`,
`Quot.sound`.

## Consumer

S1992's `S1992RebasedLocalFamily` / `S1978RebasedPaperInput` / S1978's
rebased paper object.  This file does not close S1992; it isolates the exact
remaining decoration input and disproves the literal `u -> c * u` route.
